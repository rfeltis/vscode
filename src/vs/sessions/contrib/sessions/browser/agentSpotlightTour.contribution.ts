/*---------------------------------------------------------------------------------------------
 *  Copyright (c) Microsoft Corporation. All rights reserved.
 *  Licensed under the MIT License. See License.txt in the project root for license information.
 *--------------------------------------------------------------------------------------------*/

import './media/agentSpotlightTour.css';
import * as DOM from '../../../../base/browser/dom.js';
import { status } from '../../../../base/browser/ui/aria/aria.js';
import { Disposable, DisposableStore, IDisposable, toDisposable } from '../../../../base/common/lifecycle.js';
import { localize, localize2 } from '../../../../nls.js';
import { AccessibleContentProvider, AccessibleViewProviderId, AccessibleViewType, IAccessibleViewService } from '../../../../platform/accessibility/browser/accessibleView.js';
import { AccessibleViewRegistry, IAccessibleViewImplementation } from '../../../../platform/accessibility/browser/accessibleViewRegistry.js';
import { Action2, registerAction2 } from '../../../../platform/actions/common/actions.js';
import { ICommandService } from '../../../../platform/commands/common/commands.js';
import { ContextKeyExpr, IContextKey, IContextKeyService, RawContextKey } from '../../../../platform/contextkey/common/contextkey.js';
import { IInstantiationService, ServicesAccessor } from '../../../../platform/instantiation/common/instantiation.js';
import { mainWindow } from '../../../../base/browser/window.js';
import { AccessibilityVerbositySettingId } from '../../../../workbench/contrib/accessibility/browser/accessibilityConfiguration.js';
import { AICustomizationManagementCommands, AICustomizationManagementSection } from '../../../../workbench/contrib/chat/browser/aiCustomization/aiCustomizationManagement.js';
import { ChatContextKeys } from '../../../../workbench/contrib/chat/common/actions/chatContextKeys.js';
import { ISessionsPartService } from '../../../services/sessions/browser/sessionsPartService.js';
import { ISessionsManagementService } from '../../../services/sessions/common/sessionsManagement.js';
import { IsSessionsWindowContext } from '../../../../workbench/common/contextkeys.js';
import { IWorkbenchLayoutService, Parts } from '../../../../workbench/services/layout/browser/layoutService.js';

const $ = DOM.$;

const START_AGENT_SPOTLIGHT_TOUR_ID = 'sessions.agentSpotlightTour.start';
const START_MCP_CHANGEBOARDING_SPOTLIGHT_ID = 'sessions.agentSpotlightTour.startMcpChangeboardingNudge';
const SHOW_MCP_CHANGEBOARDING_SPOTLIGHT_ID = 'sessions.agentSpotlightTour.showMcpChangeboardingSpotlight';
const OPEN_QUICK_START_CHECKLIST_ID = 'sessions.agentQuickStartChecklist.open';
const OPEN_CHOOSE_MISSION_ID = 'sessions.agentChooseMission.open';
const MCP_SERVERS_CUSTOMIZATION_TARGET_ID = 'sessions.customization.mcpServers';
const AgentSpotlightTourFocusedContext = new RawContextKey<boolean>('agentSpotlightTourFocused', false);
const CHOOSE_MISSION_PROMPT = 'Implement [feature]. Follow existing patterns in [area]. Add tests and explain tradeoffs.';

interface IAgentSpotlightStep {
	readonly targetId: string;
	readonly title: string;
	readonly body: string;
	readonly badge?: string;
	readonly primaryLabel?: string;
	readonly primaryAction?: () => void;
}

interface IAgentSpotlightCustomizationsExpander {
	expand(): void;
}

interface IAgentSpotlightRect {
	readonly left: number;
	readonly top: number;
	readonly right: number;
	readonly bottom: number;
}

interface IAgentQuickStartTask {
	readonly title: string;
	readonly description: string;
	readonly done: boolean;
}

interface IAgentMissionOption {
	readonly label: string;
	readonly custom?: boolean;
}

const agentSpotlightSteps: readonly IAgentSpotlightStep[] = [
	{
		targetId: 'sessions.customization.skills',
		title: localize('agentSpotlight.skills.title', "Customize this agent"),
		body: localize('agentSpotlight.skills.body', "You can customize this agent. Skills add capabilities you can reuse across sessions."),
	},
	{
		targetId: 'sessions.customization.mcpServers',
		title: localize('agentSpotlight.mcp.title', "Connect external tools"),
		body: localize('agentSpotlight.mcp.body', "MCP Servers are new. Connect external tools to any agent."),
	},
];

const agentSpotlightTargets = new Map<string, Set<HTMLElement>>();
const agentSpotlightCustomizationsExpanders = new Set<IAgentSpotlightCustomizationsExpander>();
const mcpChangeboardingIndicators = new Set<{ readonly element: HTMLElement; readonly button: HTMLElement }>();
let activeSpotlightTour: AgentSpotlightTour | undefined;
let activeQuickStartChecklist: AgentQuickStartChecklist | undefined;
let activeMissionChooser: AgentMissionChooser | undefined;
let mcpChangeboardingNudgeActive = false;

export function registerAgentSpotlightTarget(targetId: string, element: HTMLElement): IDisposable {
	let elements = agentSpotlightTargets.get(targetId);
	if (!elements) {
		elements = new Set();
		agentSpotlightTargets.set(targetId, elements);
	}
	elements.add(element);
	return toDisposable(() => {
		elements?.delete(element);
		if (elements?.size === 0) {
			agentSpotlightTargets.delete(targetId);
		}
	});
}

export function registerAgentSpotlightCustomizationsExpander(expander: IAgentSpotlightCustomizationsExpander): IDisposable {
	agentSpotlightCustomizationsExpanders.add(expander);
	return toDisposable(() => agentSpotlightCustomizationsExpanders.delete(expander));
}

export function registerAgentMcpChangeboardingIndicator(button: HTMLElement, element: HTMLElement): IDisposable {
	const entry = { button, element };
	mcpChangeboardingIndicators.add(entry);
	updateMcpChangeboardingIndicator(entry);
	return toDisposable(() => {
		mcpChangeboardingIndicators.delete(entry);
		element.classList.add('hidden');
		button.classList.remove('agent-mcp-changeboarding-armed');
		button.removeAttribute('aria-description');
	});
}

export function consumeAgentMcpChangeboardingNudge(): boolean {
	if (!mcpChangeboardingNudgeActive) {
		return false;
	}
	setMcpChangeboardingNudgeActive(false);
	return true;
}

class AgentSpotlightTour extends Disposable {

	private readonly _document = mainWindow.document;
	private readonly _cardDisposables = this._register(new DisposableStore());
	private readonly _focusedContextKey: IContextKey<boolean>;
	private readonly _previousFocus = DOM.isHTMLElement(this._document.activeElement) ? this._document.activeElement : undefined;
	private _stepIndex = 0;
	private _root: HTMLElement | undefined;
	private _dimmers: readonly [HTMLElement, HTMLElement, HTMLElement, HTMLElement] | undefined;
	private _highlight: HTMLElement | undefined;
	private _card: HTMLElement | undefined;
	private _arrow: HTMLElement | undefined;
	private _focusableButtons: HTMLButtonElement[] = [];
	private _activeTarget: HTMLElement | undefined;

	constructor(
		private readonly _steps: readonly IAgentSpotlightStep[],
		@IContextKeyService contextKeyService: IContextKeyService,
		@IAccessibleViewService private readonly _accessibleViewService: IAccessibleViewService,
		@IWorkbenchLayoutService private readonly _layoutService: IWorkbenchLayoutService,
	) {
		super();

		this._focusedContextKey = AgentSpotlightTourFocusedContext.bindTo(contextKeyService);
		this._register(toDisposable(() => {
			this._focusedContextKey.reset();
			this._activeTarget?.classList.remove('agent-spotlight-target-active');
			this._root?.remove();
			if (activeSpotlightTour === this) {
				activeSpotlightTour = undefined;
			}
			this._previousFocus?.focus();
		}));
	}

	start(): void {
		if (this._steps.length === 0) {
			return;
		}

		this._focusedContextKey.set(true);
		this._root = DOM.append(this._layoutService.getContainer(mainWindow), $('.agent-spotlight-tour'));
		this._root.setAttribute('aria-live', 'polite');
		this._dimmers = [
			DOM.append(this._root, $('.agent-spotlight-dim.agent-spotlight-dim-top')),
			DOM.append(this._root, $('.agent-spotlight-dim.agent-spotlight-dim-right')),
			DOM.append(this._root, $('.agent-spotlight-dim.agent-spotlight-dim-bottom')),
			DOM.append(this._root, $('.agent-spotlight-dim.agent-spotlight-dim-left')),
		];
		this._highlight = DOM.append(this._root, $('.agent-spotlight-highlight'));
		this._highlight.setAttribute('aria-hidden', 'true');

		this._register(DOM.addDisposableListener(mainWindow, 'resize', () => this._layout()));
		this._register(DOM.addDisposableListener(this._root, 'click', e => {
			if (e.target === this._root) {
				this.dispose();
			}
		}));
		this._register(DOM.addDisposableListener(this._document, 'keydown', e => this._onKeyDown(e)));
		this._showStep(0);
	}

	focus(): void {
		this._card?.focus();
	}

	private _showStep(index: number): void {
		this._stepIndex = Math.max(0, Math.min(index, this._steps.length - 1));
		this._ensureCustomizationsExpanded();
		this._updateActiveTarget();
		this._renderCard();
		this._layout();
		this.focus();

		const step = this._steps[this._stepIndex];
		status(localize('agentSpotlight.status', "{0}. {1}. {2}", this._getStepLabel(step), step.title, step.body));
	}

	private _renderCard(): void {
		this._cardDisposables.clear();
		this._card?.remove();
		this._focusableButtons = [];
		const step = this._steps[this._stepIndex];
		const card = DOM.append(this._root!, $('.agent-spotlight-card'));
		card.tabIndex = -1;
		card.setAttribute('role', 'dialog');
		card.setAttribute('aria-modal', 'true');
		card.setAttribute('aria-label', this._getCardAriaLabel(step));
		this._card = card;
		this._arrow = DOM.append(card, $('.agent-spotlight-arrow'));
		this._arrow.setAttribute('aria-hidden', 'true');

		const closeButton = this._document.createElement('button');
		card.appendChild(closeButton);
		closeButton.type = 'button';
		closeButton.classList.add('agent-spotlight-close-button');
		closeButton.textContent = 'X';
		const closeLabel = localize('agentSpotlight.close', "Close Spotlight Tour");
		closeButton.title = closeLabel;
		closeButton.setAttribute('aria-label', closeLabel);
		this._cardDisposables.add(DOM.addDisposableListener(closeButton, 'click', () => this.dispose()));
		this._focusableButtons.push(closeButton);

		const counter = DOM.append(card, $('.agent-spotlight-counter'));
		counter.textContent = this._getStepLabel(step);

		const title = DOM.append(card, $('h2.agent-spotlight-title'));
		title.textContent = step.title;

		const body = DOM.append(card, $('p.agent-spotlight-body'));
		body.textContent = step.body;

		const actions = DOM.append(card, $('.agent-spotlight-actions'));
		if (this._steps.length > 1) {
			const backButton = this._appendButton(actions, localize('agentSpotlight.back', "Back"), 'secondary', () => this._showStep(this._stepIndex - 1));
			backButton.disabled = this._stepIndex === 0;
		}
		if (this._stepIndex === this._steps.length - 1) {
			this._appendButton(actions, step.primaryLabel ?? localize('agentSpotlight.finish', "Finish"), 'primary', () => {
				const primaryAction = step.primaryAction;
				this.dispose();
				primaryAction?.();
			});
		} else {
			this._appendButton(actions, localize('agentSpotlight.next', "Next"), 'primary', () => this._showStep(this._stepIndex + 1));
		}
	}

	private _getStepLabel(step: IAgentSpotlightStep): string {
		return step.badge ?? localize('agentSpotlight.counter', "Step {0} of {1}", this._stepIndex + 1, this._steps.length);
	}

	private _getCardAriaLabel(step: IAgentSpotlightStep): string {
		const hint = this._accessibleViewService.getOpenAriaHint(AccessibilityVerbositySettingId.AgentSpotlightTour);
		if (hint) {
			return localize('agentSpotlight.ariaWithHint', "{0}. {1}. {2} {3}", this._getStepLabel(step), step.title, step.body, hint);
		}
		return localize('agentSpotlight.aria', "{0}. {1}. {2}", this._getStepLabel(step), step.title, step.body);
	}

	private _appendButton(parent: HTMLElement, label: string, kind: 'primary' | 'secondary', handler: () => void): HTMLButtonElement {
		const button = this._document.createElement('button');
		parent.appendChild(button);
		button.type = 'button';
		button.classList.add('agent-spotlight-button', `agent-spotlight-button-${kind}`);
		button.textContent = label;
		this._cardDisposables.add(DOM.addDisposableListener(button, 'click', handler));
		this._focusableButtons.push(button);
		return button;
	}

	private _layout(): void {
		const target = this._getTarget();
		target?.scrollIntoView({ block: 'center' });
		const rect = target?.getBoundingClientRect();

		if (rect && this._highlight) {
			const padding = 6;
			const left = Math.max(0, rect.left - padding);
			const top = Math.max(0, rect.top - padding);
			const right = Math.min(mainWindow.innerWidth, rect.right + padding);
			const bottom = Math.min(mainWindow.innerHeight, rect.bottom + padding);
			this._highlight.classList.remove('hidden');
			this._highlight.style.left = `${left}px`;
			this._highlight.style.top = `${top}px`;
			this._highlight.style.width = `${right - left}px`;
			this._highlight.style.height = `${bottom - top}px`;
			this._layoutDimmers({ left, top, right, bottom });
		} else {
			this._highlight?.classList.add('hidden');
			this._layoutDimmers(undefined);
		}

		if (!this._card) {
			return;
		}

		const gap = 18;
		const edgePadding = 12;
		const cardWidth = this._card.offsetWidth;
		const cardHeight = this._card.offsetHeight;
		const maxLeft = mainWindow.innerWidth - cardWidth - edgePadding;
		const maxTop = mainWindow.innerHeight - cardHeight - edgePadding;
		let left = Math.max(edgePadding, (mainWindow.innerWidth - cardWidth) / 2);
		let top = Math.max(edgePadding, (mainWindow.innerHeight - cardHeight) / 2);

		this._card.classList.remove('left-of-target', 'right-of-target', 'centered');
		if (rect) {
			const rightLeft = rect.right + gap;
			const leftLeft = rect.left - cardWidth - gap;
			if (rightLeft <= maxLeft || rect.left < mainWindow.innerWidth / 2) {
				left = Math.min(rightLeft, maxLeft);
				this._card.classList.add('right-of-target');
			} else {
				left = Math.max(edgePadding, leftLeft);
				this._card.classList.add('left-of-target');
			}
			top = Math.min(Math.max(edgePadding, rect.top + rect.height / 2 - cardHeight / 2), Math.max(edgePadding, maxTop));
			const arrowTop = Math.min(Math.max(16, rect.top + rect.height / 2 - top - 9), Math.max(16, cardHeight - 25));
			if (this._arrow) {
				this._arrow.style.top = `${arrowTop}px`;
			}
		} else {
			this._card.classList.add('centered');
			if (this._arrow) {
				this._arrow.style.top = '';
			}
		}

		this._card.style.left = `${left}px`;
		this._card.style.top = `${top}px`;
	}

	private _layoutDimmers(rect: IAgentSpotlightRect | undefined): void {
		if (!this._dimmers) {
			return;
		}

		if (!rect) {
			for (const dimmer of this._dimmers) {
				dimmer.style.left = '0px';
				dimmer.style.top = '0px';
				dimmer.style.width = `${mainWindow.innerWidth}px`;
				dimmer.style.height = `${mainWindow.innerHeight}px`;
			}
			return;
		}

		const [top, right, bottom, left] = this._dimmers;
		top.style.left = '0px';
		top.style.top = '0px';
		top.style.width = `${mainWindow.innerWidth}px`;
		top.style.height = `${rect.top}px`;

		right.style.left = `${rect.right}px`;
		right.style.top = `${rect.top}px`;
		right.style.width = `${mainWindow.innerWidth - rect.right}px`;
		right.style.height = `${rect.bottom - rect.top}px`;

		bottom.style.left = '0px';
		bottom.style.top = `${rect.bottom}px`;
		bottom.style.width = `${mainWindow.innerWidth}px`;
		bottom.style.height = `${mainWindow.innerHeight - rect.bottom}px`;

		left.style.left = '0px';
		left.style.top = `${rect.top}px`;
		left.style.width = `${rect.left}px`;
		left.style.height = `${rect.bottom - rect.top}px`;
	}

	private _getTarget(): HTMLElement | undefined {
		const step = this._steps[this._stepIndex];
		return getAgentSpotlightTarget(step.targetId);
	}

	private _updateActiveTarget(): void {
		this._activeTarget?.classList.remove('agent-spotlight-target-active');
		this._activeTarget = this._getTarget();
		this._activeTarget?.classList.add('agent-spotlight-target-active');
	}

	private _ensureCustomizationsExpanded(): void {
		for (const expander of agentSpotlightCustomizationsExpanders) {
			expander.expand();
		}
	}

	private _onKeyDown(e: KeyboardEvent): void {
		if (e.key === 'Escape') {
			e.preventDefault();
			this.dispose();
			return;
		}
		if (e.key === 'ArrowRight') {
			e.preventDefault();
			if (this._stepIndex < this._steps.length - 1) {
				this._showStep(this._stepIndex + 1);
			}
			return;
		}
		if (e.key === 'ArrowLeft') {
			e.preventDefault();
			if (this._stepIndex > 0) {
				this._showStep(this._stepIndex - 1);
			}
			return;
		}
		if (e.key === 'Tab') {
			this._trapFocus(e);
		}
	}

	private _trapFocus(e: KeyboardEvent): void {
		if (!this._card) {
			return;
		}

		const focusable = this._focusableButtons.filter(button => !button.disabled);
		if (focusable.length === 0) {
			e.preventDefault();
			this.focus();
			return;
		}

		const activeElement = this._document.activeElement;
		const currentIndex = focusable.indexOf(activeElement as HTMLButtonElement);
		if (e.shiftKey && currentIndex <= 0) {
			e.preventDefault();
			focusable[focusable.length - 1].focus();
		} else if (!e.shiftKey && currentIndex === focusable.length - 1) {
			e.preventDefault();
			focusable[0].focus();
		}
	}
}

class AgentQuickStartChecklist extends Disposable {

	private readonly _document = mainWindow.document;
	private readonly _focusedContextKey: IContextKey<boolean>;
	private readonly _previousFocus = DOM.isHTMLElement(this._document.activeElement) ? this._document.activeElement : undefined;
	private _root: HTMLElement | undefined;

	constructor(
		@IContextKeyService contextKeyService: IContextKeyService,
		@IWorkbenchLayoutService private readonly _layoutService: IWorkbenchLayoutService,
	) {
		super();

		this._focusedContextKey = AgentSpotlightTourFocusedContext.bindTo(contextKeyService);
		this._register(toDisposable(() => {
			this._focusedContextKey.reset();
			this._root?.remove();
			if (activeQuickStartChecklist === this) {
				activeQuickStartChecklist = undefined;
			}
			this._previousFocus?.focus();
		}));
	}

	start(): void {
		this._focusedContextKey.set(true);
		this._root = DOM.append(this._layoutService.getContainer(mainWindow), $('.agent-quick-start-checklist'));
		this._root.tabIndex = -1;
		this._root.setAttribute('role', 'dialog');
		this._root.setAttribute('aria-label', localize('agentQuickStart.aria', "Quick Start checklist. 2 of 4 tasks complete."));
		this._render();
		this._register(DOM.addDisposableListener(this._document, 'keydown', e => {
			if (e.key === 'Escape') {
				e.preventDefault();
				this.dispose();
			}
		}));
		this.focus();
		status(localize('agentQuickStart.status', "Quick Start checklist opened. 2 of 4 tasks complete."));
	}

	focus(): void {
		this._root?.focus();
	}

	private _render(): void {
		const root = this._root!;

		const closeButton = this._document.createElement('button');
		root.appendChild(closeButton);
		closeButton.type = 'button';
		closeButton.classList.add('agent-quick-start-close-button');
		closeButton.textContent = 'X';
		const closeLabel = localize('agentQuickStart.close', "Close Quick Start Checklist");
		closeButton.title = closeLabel;
		closeButton.setAttribute('aria-label', closeLabel);
		this._register(DOM.addDisposableListener(closeButton, 'click', () => this.dispose()));

		const header = DOM.append(root, $('.agent-quick-start-header'));
		const title = DOM.append(header, $('h2.agent-quick-start-title'));
		title.textContent = localize('agentQuickStart.title', "Quick Start");

		const progress = DOM.append(header, $('.agent-quick-start-progress'));
		progress.textContent = localize('agentQuickStart.progress', "2/4");

		const description = DOM.append(root, $('p.agent-quick-start-description'));
		description.textContent = localize('agentQuickStart.description', "Complete these starter tasks to get productive with Agents.");

		const list = DOM.append(root, $('ul.agent-quick-start-tasks'));
		list.setAttribute('aria-label', localize('agentQuickStart.tasksLabel', "Quick Start tasks"));
		for (const task of this._getTasks()) {
			this._appendTask(list, task);
		}
	}

	private _appendTask(parent: HTMLElement, task: IAgentQuickStartTask): void {
		const item = DOM.append(parent, $('li.agent-quick-start-task'));
		item.classList.toggle('done', task.done);
		item.setAttribute('aria-label', task.done
			? localize('agentQuickStart.taskDone', "Completed: {0}. {1}", task.title, task.description)
			: localize('agentQuickStart.taskPending', "Not completed: {0}. {1}", task.title, task.description));

		const check = DOM.append(item, $('span.agent-quick-start-check'));
		check.setAttribute('aria-hidden', 'true');
		if (task.done) {
			check.classList.add('codicon', 'codicon-check');
		}

		const content = DOM.append(item, $('span.agent-quick-start-task-content'));
		const title = DOM.append(content, $('strong'));
		title.textContent = task.title;
		const description = DOM.append(content, $('small'));
		description.textContent = task.description;
	}

	private _getTasks(): readonly IAgentQuickStartTask[] {
		return [
			{
				title: localize('agentQuickStart.model.title', "Choose your model"),
				description: localize('agentQuickStart.model.description', "Match speed and reasoning depth to the task."),
				done: true,
			},
			{
				title: localize('agentQuickStart.agents.title', "Browse Agents"),
				description: localize('agentQuickStart.agents.description', "Find reusable roles before writing a prompt from scratch."),
				done: true,
			},
			{
				title: localize('agentQuickStart.skills.title', "Add or browse Skills"),
				description: localize('agentQuickStart.skills.description', "Give agents repeatable know-how for common workflows."),
				done: false,
			},
			{
				title: localize('agentQuickStart.session.title', "Start a new session"),
				description: localize('agentQuickStart.session.description', "Put the chosen model, agent, and skill into action."),
				done: false,
			},
		];
	}
}

class AgentMissionChooser extends Disposable {

	private readonly _document = mainWindow.document;
	private readonly _focusedContextKey: IContextKey<boolean>;
	private readonly _previousFocus = DOM.isHTMLElement(this._document.activeElement) ? this._document.activeElement : undefined;
	private _root: HTMLElement | undefined;
	private _buttons: HTMLButtonElement[] = [];

	constructor(
		@IContextKeyService contextKeyService: IContextKeyService,
		@IWorkbenchLayoutService private readonly _layoutService: IWorkbenchLayoutService,
		@ISessionsPartService private readonly _sessionsPartService: ISessionsPartService,
		@ISessionsManagementService private readonly _sessionsManagementService: ISessionsManagementService,
	) {
		super();

		this._focusedContextKey = AgentSpotlightTourFocusedContext.bindTo(contextKeyService);
		this._register(toDisposable(() => {
			this._focusedContextKey.reset();
			this._root?.remove();
			if (activeMissionChooser === this) {
				activeMissionChooser = undefined;
			}
			if (!(DOM.isHTMLElement(this._document.activeElement) && this._document.activeElement.classList.contains('native-edit-context'))) {
				this._previousFocus?.focus();
			}
		}));
	}

	start(): void {
		this._focusedContextKey.set(true);
		this._root = DOM.append(this._layoutService.getContainer(mainWindow), $('.agent-mission-chooser'));
		this._root.tabIndex = -1;
		this._root.setAttribute('role', 'dialog');
		this._root.setAttribute('aria-label', localize('agentMissionChooser.aria', "Choose Your Mission. Pick what you want your agent to help with."));
		this._render();
		this._register(DOM.addDisposableListener(mainWindow, 'resize', () => this._layout()));
		this._register(DOM.addDisposableListener(this._document, 'keydown', e => {
			if (e.key === 'Escape') {
				e.preventDefault();
				this.dispose();
			}
		}));
		this._layout();
		this.focus();
		status(localize('agentMissionChooser.status', "Choose Your Mission opened."));
	}

	focus(): void {
		(this._buttons[0] ?? this._root)?.focus();
	}

	private _render(): void {
		const root = this._root!;
		const title = DOM.append(root, $('h2.agent-mission-title'));
		title.textContent = localize('agentMissionChooser.title', "What do you want your agent to help with?");

		const grid = DOM.append(root, $('.agent-mission-grid'));
		grid.setAttribute('aria-label', localize('agentMissionChooser.optionsLabel', "Mission options"));
		for (const option of this._getOptions()) {
			this._appendOption(grid, option);
		}
	}

	private _appendOption(parent: HTMLElement, option: IAgentMissionOption): void {
		const button = this._document.createElement('button');
		parent.appendChild(button);
		button.type = 'button';
		button.classList.add('agent-mission-option');
		if (option.custom) {
			button.classList.add('custom-prompt');
		}
		button.textContent = option.label;
		this._register(DOM.addDisposableListener(button, 'click', () => this._selectMission()));
		this._buttons.push(button);
	}

	private _selectMission(): void {
		const activeSession = this._sessionsManagementService.activeSession.get();
		const view = this._sessionsPartService.getSessionView(activeSession?.sessionId)
			?? this._sessionsPartService.getSessionView(undefined);
		view?.prefillInput(CHOOSE_MISSION_PROMPT);
		this.dispose();
		status(localize('agentMissionChooser.selectedStatus', "Mission prompt added to the chat input."));
	}

	private _getOptions(): readonly IAgentMissionOption[] {
		return [
			{ label: localize('agentMissionChooser.implementFeature', "Implement feature") },
			{ label: localize('agentMissionChooser.investigateBug', "Investigate bug") },
			{ label: localize('agentMissionChooser.reviewChanges', "Review changes") },
			{ label: localize('agentMissionChooser.diagnoseCi', "Diagnose CI") },
			{ label: localize('agentMissionChooser.enterPrompt', "Enter my own prompt"), custom: true },
		];
	}

	private _layout(): void {
		if (!this._root) {
			return;
		}

		const target = this._getInputTarget();
		const edgePadding = 16;
		const gap = 24;
		const fallbackWidth = Math.min(520, mainWindow.innerWidth - edgePadding * 2);
		const targetRect = target?.getBoundingClientRect();
		const width = targetRect ? Math.min(Math.max(320, targetRect.width), mainWindow.innerWidth - edgePadding * 2) : fallbackWidth;

		this._root.style.width = `${width}px`;

		const height = this._root.offsetHeight;
		let left = targetRect ? targetRect.left + (targetRect.width - width) / 2 : (mainWindow.innerWidth - width) / 2;
		left = Math.min(Math.max(edgePadding, left), mainWindow.innerWidth - width - edgePadding);

		let top = targetRect ? targetRect.top - height - gap : mainWindow.innerHeight - height - 180;
		top = Math.min(Math.max(edgePadding, top), mainWindow.innerHeight - height - edgePadding);

		this._root.style.left = `${left}px`;
		this._root.style.top = `${top}px`;
	}

	private _getInputTarget(): HTMLElement | undefined {
		const activeSession = this._sessionsManagementService.activeSession.get();
		return (this._sessionsPartService.getSessionView(activeSession?.sessionId)
			?? this._sessionsPartService.getSessionView(undefined))?.getInputTargetElement();
	}
}

class AgentSpotlightTourAccessibilityHelp implements IAccessibleViewImplementation {
	readonly priority = 100;
	readonly name = 'agent-spotlight-tour';
	readonly type = AccessibleViewType.Help;
	readonly when = AgentSpotlightTourFocusedContext;

	getProvider(): AccessibleContentProvider {
		return new AccessibleContentProvider(
			AccessibleViewProviderId.AgentSpotlightTour,
			{ type: AccessibleViewType.Help },
			() => [
				localize('agentSpotlight.help.overview', "You are in an Agents window onboarding demo."),
				localize('agentSpotlight.help.navigate', "- Use Tab and Shift+Tab to move between demo controls."),
				localize('agentSpotlight.help.steps', "- Use Left Arrow and Right Arrow to move between spotlight steps."),
				localize('agentSpotlight.help.dismiss', "- Press Escape or the Close button to close the active demo."),
				localize('agentSpotlight.help.mission', "- In Choose Your Mission, select a mission to add a sample implementation prompt to the chat input."),
				localize('agentSpotlight.help.start', "- Run Start Onboarding Spotlight Tour, Start MCP Changeboarding Spotlight Nudge, Open Quick Start Checklist, or Open Choose Your Mission from the Command Palette to start a demo. The MCP nudge marks MCP Servers with a green dot; open MCP Servers to show the spotlight."),
			].join('\n'),
			() => {
				if (activeMissionChooser) {
					activeMissionChooser.focus();
				} else if (activeQuickStartChecklist) {
					activeQuickStartChecklist.focus();
				} else {
					activeSpotlightTour?.focus();
				}
			},
			AccessibilityVerbositySettingId.AgentSpotlightTour,
		);
	}
}

function getMcpChangeboardingSpotlightSteps(primaryAction: () => void): readonly IAgentSpotlightStep[] {
	return [
		{
			targetId: MCP_SERVERS_CUSTOMIZATION_TARGET_ID,
			badge: localize('agentSpotlight.changeboarding.badge', "New Feature"),
			title: localize('agentSpotlight.changeboarding.mcp.title', "MCP Servers are new"),
			body: localize('agentSpotlight.changeboarding.mcp.body', "Connect external tools to any agent."),
			primaryLabel: localize('agentSpotlight.gotIt', "Got It"),
			primaryAction,
		},
	];
}

function setMcpChangeboardingNudgeActive(active: boolean): void {
	mcpChangeboardingNudgeActive = active;
	for (const entry of mcpChangeboardingIndicators) {
		updateMcpChangeboardingIndicator(entry);
	}
}

function updateMcpChangeboardingIndicator(entry: { readonly element: HTMLElement; readonly button: HTMLElement }): void {
	entry.element.classList.toggle('hidden', !mcpChangeboardingNudgeActive);
	entry.button.classList.toggle('agent-mcp-changeboarding-armed', mcpChangeboardingNudgeActive);
	if (mcpChangeboardingNudgeActive) {
		entry.button.setAttribute('aria-description', localize('agentSpotlight.changeboarding.mcp.ariaDescription', "New feature. Open MCP Servers to learn more."));
	} else {
		entry.button.removeAttribute('aria-description');
	}
}

function getAgentSpotlightTarget(targetId: string): HTMLElement | undefined {
	for (const candidate of agentSpotlightTargets.get(targetId) ?? []) {
		if (candidate.isConnected) {
			return candidate;
		}
	}
	return undefined;
}

function ensureCustomizationsExpanded(): void {
	for (const expander of agentSpotlightCustomizationsExpanders) {
		expander.expand();
	}
}

function startAgentSpotlightExperience(accessor: ServicesAccessor, steps: readonly IAgentSpotlightStep[]): void {
	const layoutService = accessor.get(IWorkbenchLayoutService);
	layoutService.setPartHidden(false, Parts.SIDEBAR_PART);

	activeMissionChooser?.dispose();
	activeQuickStartChecklist?.dispose();
	activeSpotlightTour?.dispose();
	activeSpotlightTour = accessor.get(IInstantiationService).createInstance(AgentSpotlightTour, steps);
	activeSpotlightTour.start();
}

function showMcpChangeboardingNudge(accessor: ServicesAccessor): void {
	const layoutService = accessor.get(IWorkbenchLayoutService);
	layoutService.setPartHidden(false, Parts.SIDEBAR_PART);
	ensureCustomizationsExpanded();
	activeMissionChooser?.dispose();
	activeQuickStartChecklist?.dispose();
	activeSpotlightTour?.dispose();
	if (!getAgentSpotlightTarget(MCP_SERVERS_CUSTOMIZATION_TARGET_ID)) {
		setMcpChangeboardingNudgeActive(false);
		status(localize('agentSpotlight.changeboarding.mcp.nudgeUnavailable', "MCP Servers is not visible in the Customizations sidebar."));
		return;
	}
	setMcpChangeboardingNudgeActive(true);
	status(localize('agentSpotlight.changeboarding.mcp.nudgeStatus', "MCP Servers is marked as new. Open MCP Servers to learn more."));
}

function openQuickStartChecklist(accessor: ServicesAccessor): void {
	activeSpotlightTour?.dispose();
	activeMissionChooser?.dispose();
	activeQuickStartChecklist?.dispose();
	activeQuickStartChecklist = accessor.get(IInstantiationService).createInstance(AgentQuickStartChecklist);
	activeQuickStartChecklist.start();
}

function openMissionChooser(accessor: ServicesAccessor): void {
	activeSpotlightTour?.dispose();
	activeQuickStartChecklist?.dispose();
	activeMissionChooser?.dispose();
	activeMissionChooser = accessor.get(IInstantiationService).createInstance(AgentMissionChooser);
	activeMissionChooser.start();
}

registerAction2(class StartAgentSpotlightTourAction extends Action2 {
	constructor() {
		super({
			id: START_AGENT_SPOTLIGHT_TOUR_ID,
			title: localize2('agentSpotlight.start', "Start Onboarding Spotlight Tour"),
			f1: true,
			precondition: ContextKeyExpr.and(IsSessionsWindowContext, ChatContextKeys.enabled),
		});
	}

	run(accessor: ServicesAccessor): void {
		startAgentSpotlightExperience(accessor, agentSpotlightSteps);
	}
});

registerAction2(class StartMcpChangeboardingSpotlightAction extends Action2 {
	constructor() {
		super({
			id: START_MCP_CHANGEBOARDING_SPOTLIGHT_ID,
			title: localize2('agentSpotlight.startMcpChangeboarding', "Start MCP Changeboarding Spotlight Nudge"),
			f1: true,
			precondition: ContextKeyExpr.and(IsSessionsWindowContext, ChatContextKeys.enabled),
		});
	}

	run(accessor: ServicesAccessor): void {
		showMcpChangeboardingNudge(accessor);
	}
});

registerAction2(class ShowMcpChangeboardingSpotlightAction extends Action2 {
	constructor() {
		super({
			id: SHOW_MCP_CHANGEBOARDING_SPOTLIGHT_ID,
			title: localize2('agentSpotlight.showMcpChangeboarding', "Show MCP Changeboarding Spotlight"),
			precondition: ContextKeyExpr.and(IsSessionsWindowContext, ChatContextKeys.enabled),
		});
	}

	run(accessor: ServicesAccessor): void {
		const commandService = accessor.get(ICommandService);
		startAgentSpotlightExperience(accessor, getMcpChangeboardingSpotlightSteps(() => {
			void commandService.executeCommand(AICustomizationManagementCommands.OpenEditor, AICustomizationManagementSection.McpServers);
		}));
	}
});

registerAction2(class OpenQuickStartChecklistAction extends Action2 {
	constructor() {
		super({
			id: OPEN_QUICK_START_CHECKLIST_ID,
			title: localize2('agentQuickStart.open', "Open Quick Start Checklist"),
			f1: true,
			precondition: ContextKeyExpr.and(IsSessionsWindowContext, ChatContextKeys.enabled),
		});
	}

	run(accessor: ServicesAccessor): void {
		openQuickStartChecklist(accessor);
	}
});

registerAction2(class OpenChooseMissionAction extends Action2 {
	constructor() {
		super({
			id: OPEN_CHOOSE_MISSION_ID,
			title: localize2('agentMissionChooser.open', "Open Choose Your Mission"),
			f1: true,
			precondition: ContextKeyExpr.and(IsSessionsWindowContext, ChatContextKeys.enabled),
		});
	}

	run(accessor: ServicesAccessor): void {
		openMissionChooser(accessor);
	}
});

AccessibleViewRegistry.register(new AgentSpotlightTourAccessibilityHelp());
