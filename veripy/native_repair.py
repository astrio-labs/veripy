"""Live proof-only repair controller for native verifier adapters.

An adapter owns parsing, preservation checks, solver calls and annotation
pruning. This controller verifies before generation and never feeds a failed
pruning variant back as the replacement candidate. It does not translate Python
or relax the sidecar policy of :mod:`veripy.repair`.
"""
from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Callable, Protocol


class NativeAdapter(Protocol):
    def assess(self, source: str, folder: Path) -> dict[str, Any]: ...
    def accepted(self, observation: dict[str, Any]) -> bool: ...
    def feedback(self, observation: dict[str, Any], mode: str) -> str: ...
    def prune(self, source: str, observation: dict[str, Any], folder: Path,
              budget: int) -> dict[str, Any]: ...


class NativeEngineError(RuntimeError):
    """A recorded model dispatch failed; no automatic retry is allowed."""


class NativeProposalError(ValueError):
    """A model returned malformed edits; consume the response and give feedback."""
    def __init__(self, message: str, proposal: str):
        super().__init__(message)
        self.proposal = proposal


def repair_native(
    original: str, folder: Path, adapter: NativeAdapter,
    engine: Callable[[dict[str, Any], Path], str], *,
    feedback_mode: str = 'structured', max_responses: int = 5,
    pruning_budget: int = 8,
    expose_diagnostic_experiments: bool = False,
    allow_annotation_syntax_repair: bool = False,
    preflight: dict[str, Any] | None = None,
    initial: tuple[str, dict[str, Any]] | None = None,
) -> dict[str, Any]:
    """Run one arm with a task-total pruning budget, including the initial reply.

    Optional preflight and initial observations must be trusted adapter results
    for this exact original program. A paired evaluator can share them between
    arms. ``responses`` counts that shared response in each arm's budget;
    ``model_dispatches`` counts only dispatches performed by this invocation.
    Output directories must be new, preventing accidental overwrite or retries.
    """
    if feedback_mode not in {'raw', 'structured'}:
        raise ValueError('feedback_mode must be raw or structured')
    if max_responses < 1 or pruning_budget < 0:
        raise ValueError('max_responses must be positive and pruning_budget nonnegative')
    folder.mkdir(parents=True, exist_ok=False)
    result = dict(success=False, status='budget_exhausted', responses=0,
                  model_dispatches=0, pruning_variants=0, pruning_verifier_calls=0,
                  pruning_verifier_seconds=0.0, generated_verifier_calls=0,
                  preflight_shared=preflight is not None, initial_shared=initial is not None)
    def finish(status: str, success: bool = False, source: str | None = None):
        result.update(status=status, success=success)
        if source is not None:
            path = folder/'accepted.dfy'; path.write_text(source)
            result['candidate'] = str(path)
        (folder/'result.json').write_text(json.dumps(result, indent=2)+'\n')
        return result

    if preflight is None:
        preflight = adapter.assess(original, folder/'preflight')
    (folder/'preflight.json').write_text(json.dumps(preflight, indent=2)+'\n')
    result['input_verified'] = adapter.accepted(preflight)
    if result['input_verified']:
        return finish('input_already_verified', True, original)
    result['input_parse_failed'] = preflight.get('parse_ok') is False
    syntax_restoration = allow_annotation_syntax_repair and result['input_parse_failed']
    if (not preflight['guard']['ok'] and not syntax_restoration) or not preflight['upstream_checks']['no_avoid_verify']:
        return finish('input_rejected_by_guard')
    result['annotation_syntax_repair_allowed'] = syntax_restoration

    history: list[dict[str, Any]] = []
    for response in range(1, max_responses+1):
        result['responses'] = response
        step = folder/f'response-{response}'
        if response == 1 and initial is not None:
            source, observation = initial
        else:
            request = dict(original=original, response=response, history=list(history))
            result['model_dispatches'] += 1
            try:
                source = engine(request, step)
            except NativeProposalError as exc:
                step.mkdir(parents=True, exist_ok=True)
                rejection = {'candidate': exc.proposal, 'feedback': 'Invalid proof edit plan: '+str(exc)}
                (step/'proposal-rejection.json').write_text(json.dumps(rejection, indent=2)+'\n')
                history.append(rejection)
                result['proposal_rejections'] = result.get('proposal_rejections', 0)+1
                continue
            except NativeEngineError as exc:
                result['engine_error'] = str(exc)
                return finish('engine_failure')
            observation = adapter.assess(source, step/'assessment')
            result['generated_verifier_calls'] += 1
        if adapter.accepted(observation):
            return finish('initial_verified' if response == 1 else 'repaired', True, source)

        remaining = pruning_budget-result['pruning_variants']
        pruning_note = None
        experiments = None
        if remaining and observation['guard']['ok'] and observation['upstream_checks']['no_avoid_verify']:
            pruned = adapter.prune(source, observation, step/'pruning', remaining)
            used = len(pruned['attempts'])
            if expose_diagnostic_experiments:
                from .proof_diagnostics import diagnostic_experiments
                experiments = diagnostic_experiments(source, observation, pruned['attempts'])
                (step/'diagnostic-experiments.json').write_text(json.dumps(experiments, indent=2)+'\n')
            if used > remaining or pruned['verifier_calls'] > used:
                raise RuntimeError('Adapter exceeded pruning budget')
            result['pruning_variants'] += used
            result['pruning_verifier_calls'] += pruned['verifier_calls']
            result['pruning_verifier_seconds'] += pruned['verifier_seconds']
            if pruned['accepted']:
                if not pruned['attempts'] or not adapter.accepted(pruned['attempts'][-1]):
                    raise RuntimeError('Adapter returned an unverified pruning result')
                return finish('pruned_verified', True, Path(pruned['candidate']).read_text())
            pruning_note = {'variants_tried': used, 'accepted': False,
                            'remaining_budget': pruning_budget-result['pruning_variants']}
        # Keep the generated candidate and its matching diagnostics. Failed
        # deletion trials cannot silently change the next model's starting point.
        entry = {'candidate': source, 'feedback': adapter.feedback(observation, feedback_mode)}
        if pruning_note is not None:
            entry['pruning'] = pruning_note
        if experiments is not None:
            entry['diagnostic_experiments'] = experiments
        history.append(entry)
    return finish('budget_exhausted')
