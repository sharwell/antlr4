/*
 [The "BSD license"]
  Copyright (c) 2012 Terence Parr
  Copyright (c) 2012 Sam Harwell
  All rights reserved.

  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions
  are met:

  1. Redistributions of source code must retain the above copyright
     notice, this list of conditions and the following disclaimer.
  2. Redistributions in binary form must reproduce the above copyright
     notice, this list of conditions and the following disclaimer in the
     documentation and/or other materials provided with the distribution.
  3. The name of the author may not be used to endorse or promote products
     derived from this software without specific prior written permission.

  THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
  IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
  OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
  NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
  THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package org.antlr.v4.runtime;

import org.antlr.v4.runtime.atn.ATNState;
import org.antlr.v4.runtime.atn.AtomTransition;
import org.antlr.v4.runtime.atn.DecisionState;
import org.antlr.v4.runtime.atn.ForestParserATNSimulator;
import org.antlr.v4.runtime.atn.NotSetTransition;
import org.antlr.v4.runtime.atn.PredictionContext;
import org.antlr.v4.runtime.atn.PredictionContext.IdentityHashMap;
import org.antlr.v4.runtime.atn.PredictionContextCache;
import org.antlr.v4.runtime.atn.RangeTransition;
import org.antlr.v4.runtime.atn.RuleStartState;
import org.antlr.v4.runtime.atn.RuleStopState;
import org.antlr.v4.runtime.atn.RuleTransition;
import org.antlr.v4.runtime.atn.SetTransition;
import org.antlr.v4.runtime.atn.Transition;
import org.antlr.v4.runtime.misc.MultiMap;
import org.antlr.v4.runtime.misc.NotNull;
import org.antlr.v4.runtime.tree.ParseTree;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 *
 * @author Sam Harwell
 */
public class ForestParser<Symbol extends Token> extends Recognizer<Symbol, ForestParserATNSimulator<Symbol>> {
	// -J-Dorg.antlr.v4.runtime.ForestParser.level=FINE
	private static final Logger LOGGER = Logger.getLogger(ForestParser.class.getName());

	private final Parser<Symbol> _parser;
	private final PredictionContextCache _contextCache = new PredictionContextCache();
	private final List<ParserState<Symbol>> _states = new ArrayList<ParserState<Symbol>>();

	public ForestParser(Parser<Symbol> parser) {
		_parser = parser;
		_interp = new ForestParserATNSimulator<Symbol>(this, parser.getATN());
	}

	public ParseTree<Symbol> parse(int entryRule) {
		getInterpreter().disable_global_context = true;
		getInterpreter().force_global_context = false;
		getInterpreter().always_try_local_context = true;

		getInterpreter().optimize_unique_closure = _parser.getInterpreter().optimize_unique_closure;
		getInterpreter().optimize_ll1 = _parser.getInterpreter().optimize_unique_closure;
		getInterpreter().optimize_hidden_conflicted_configs = _parser.getInterpreter().optimize_hidden_conflicted_configs;
		getInterpreter().optimize_tail_calls = _parser.getInterpreter().optimize_tail_calls;
		getInterpreter().tail_call_preserves_sll = _parser.getInterpreter().tail_call_preserves_sll;
		getInterpreter().treat_sllk1_conflict_as_ambiguity = true;

		final RuleStartState startState = getATN().ruleToStartState[entryRule];
		final RuleStopState stopState = getATN().ruleToStopState[entryRule];

		_states.add(new ParserState<Symbol>(startState, PredictionContext.EMPTY_FULL, PredictionContext.EMPTY_FULL, 0));

		ParserProgress progress = ParserProgress.EPSILON;
		while (progress != ParserProgress.COMPLETE) {
			switch (progress) {
			case EPSILON:
				/* At this point, each ParserState will be in the first ATNState after consuming a symbol which is one of:
				 *  - RuleStopState
				 *  - DecisionState
				 *  - State with only outgoing match transitions (atom, range, set, wildcard)
				 *
				 * We take epsilon steps until each ParserState is in one of the following:
				 *  - stopState with empty context (done parsing)
				 *  - DecisionState
				 */
				progress = parseEpsilon();
				continue;

			case NEXT_SYMBOL:
				progress = parseNextSymbol();
				continue;

			default:
				throw new IllegalStateException();
			}
		}

		if (LOGGER.isLoggable(Level.FINE)) {
			BigInteger treeCount = BigInteger.ZERO;
			for (ParserState<?> state : _states) {
				treeCount = treeCount.add(getTreeCount(state._trace));
			}

			if (!treeCount.equals(BigInteger.ONE)) {
				LOGGER.log(Level.FINE, "{0}: Forest parser found {1} trees.", new Object[] { getInputStream().getSourceName(), treeCount });
			}
		}

		if (_states.isEmpty()) {
			return ParserRuleContext.emptyContext();
		}

		if (_states.size() == 1) {
			return ParserRuleContext.emptyContext();
		}

		return ParserRuleContext.emptyContext();
	}

	public Parser<Symbol> getParser() {
		return _parser;
	}

	@Override
	public String[] getTokenNames() {
		return _parser.getTokenNames();
	}

	@Override
	public String[] getRuleNames() {
		return _parser.getRuleNames();
	}

	@Override
	public String getGrammarFileName() {
		return _parser.getGrammarFileName();
	}

	@Override
	public TokenStream<? extends Symbol> getInputStream() {
		return _parser.getInputStream();
	}

	public void setInputStream(TokenStream<? extends Symbol> input) {
		_parser.setInputStream(input);
	}

	public void reset() {
		TokenStream<?> inputStream = getInputStream();
		if (inputStream != null) {
			inputStream.seek(0);
		}

		getInterpreter().reset();
	}

	@Override
	public ParserErrorListener<? super Symbol> getErrorListenerDispatch() {
		return _parser.getErrorListenerDispatch();
	}

	@Override
	public boolean sempred(RuleContext<Symbol> _localctx, int ruleIndex, int actionIndex) {
		return _parser.sempred(_localctx, ruleIndex, actionIndex);
	}

	@Override
	public boolean precpred(RuleContext<Symbol> localctx, int precedence) {
		throw new UnsupportedOperationException("not implemented yet");
	}

	@Override
	public void action(RuleContext<Symbol> _localctx, int ruleIndex, int actionIndex) {
		throw new UnsupportedOperationException("not implemented yet");
	}

	private ParserProgress parseNextSymbol() {
		// everything here is either going to be completed or at a match transition
		int t = getInputStream().LA(1);

		for (int i = 0; i < _states.size(); i++) {
			ParserState<Symbol> state = _states.get(i);
			if (state._state instanceof RuleStopState) {
				assert state._context.isEmpty();
				continue;
			}

			assert !state._state.onlyHasEpsilonTransitions();
			assert state._state.getNumberOfTransitions() == 1;
			Transition transition = state._state.transition(0);
			switch (transition.getSerializationType()) {
			case Transition.ATOM:
			{
				AtomTransition atom = (AtomTransition)transition;
				if (t != atom.label) {
					_states.set(i, null);
					continue;
				}

				break;
			}

			case Transition.RANGE:
			{
				RangeTransition range = (RangeTransition)transition;
				if (t < range.from || t > range.to) {
					_states.set(i, null);
					continue;
				}

				break;
			}

			case Transition.SET:
			{
				SetTransition set = (SetTransition)transition;
				if (!set.label().contains(t)) {
					_states.set(i, null);
					continue;
				}

				break;
			}

			case Transition.NOT_SET:
			{
				NotSetTransition notset = (NotSetTransition)transition;
				if (notset.label().contains(t)) {
					_states.set(i, null);
					continue;
				}

				break;
			}

			case Transition.WILDCARD:
				break;

			default:
				throw new IllegalStateException();
			}

			ParserState<Symbol> nextState = new ParserState<Symbol>(transition.target, state._context, state._trace, state._depth);
			_states.set(i, nextState);
		}

		// remove all null entries
		int j = 0;
		for (int i = 0; i < _states.size(); i++) {
			if (_states.get(i) == null) {
				continue;
			}

			if (i != j) {
				_states.set(j, _states.get(i));
			}

			j++;
		}

		_states.subList(j, _states.size()).clear();

		getInputStream().consume();
		_predictions.clear();
		return ParserProgress.EPSILON;
	}

	private final Map<Integer, BitSet> _predictions = new HashMap<Integer, BitSet>();

	private ParserProgress parseEpsilon() {
		Symbol lt1 = null;

		// move everything forward has epsilon outgoing transitions but isn't at a RuleStopState
		boolean canContinue = false;
		boolean hasUnfinishedRuleStopState = false;
		boolean changed = false;
		for (int i = 0; i < _states.size(); i++) {
			final ParserState<Symbol> state = _states.get(i);
			if (state._state instanceof RuleStopState) {
				if (state._context.hasEmpty() && !state._context.isEmpty()) {
					throw new UnsupportedOperationException("Not yet implemented.");
				}

				boolean complete = state._context.hasEmpty();
				hasUnfinishedRuleStopState |= !complete;
				canContinue |= !complete;
				continue;
			}

			canContinue = true;
			if (state._state.onlyHasEpsilonTransitions()) {
				int decision = state._state instanceof DecisionState ? ((DecisionState)state._state).decision : -1;

				BitSet alts = decision >= 0 ? _predictions.get(decision) : null;
				if (alts == null && state._state.getNumberOfTransitions() > 1) {
					try {
						alts = getInterpreter().adaptivePredict(getInputStream(), decision, null);
						_predictions.put(decision, alts);
					} catch (RecognitionException ex) {
						_states.remove(i);
						i--;
						continue;
					}
				}

				boolean replacedOriginal = false;
				for (int j = 0; j < state._state.getNumberOfTransitions(); j++) {
					if (alts != null && !alts.get(j + 1)) {
						continue;
					}

					PredictionContext nextTrace = state._trace;
					if (state._state.getNumberOfTransitions() > 1) {
						nextTrace = PredictionContextCache.UNCACHED.getChild(state._trace, j + 1);
					}

					ParserState<Symbol> nextState;
					Transition transition = state._state.transition(j);
					switch (transition.getSerializationType()) {
					case Transition.ACTION:
					case Transition.PRECEDENCE:
					case Transition.PREDICATE:
					case Transition.EPSILON:
						nextState = new ParserState<Symbol>(transition.target, state._context, nextTrace, state._depth);
						break;

					case Transition.RULE:
					{
						if (lt1 == null) {
							lt1 = getInputStream().LT(1);
						}

						assert state._state.getNumberOfTransitions() == 1 && state._state.transition(0) instanceof RuleTransition;
						ATNState returnState = ((RuleTransition)state._state.transition(0)).followState;
						PredictionContext context = _contextCache.getChild(state._context, returnState.stateNumber);
						nextState = new ParserState<Symbol>(transition.target, context, nextTrace, state._depth + 1);
						break;
					}

					default:
						throw new IllegalStateException();
					}

					changed = true;
					if (!replacedOriginal) {
						_states.set(i, nextState);
						replacedOriginal = true;
					} else {
						_states.add(nextState);
					}
				}

				if (!replacedOriginal) {
					_states.remove(i);
					i--;
				}
			} else {
				// begin debug check
				for (int j = 0; j < state._state.getNumberOfTransitions(); j++) {
					switch (state._state.transition(j).getSerializationType()) {
					case Transition.ATOM:
					case Transition.RANGE:
					case Transition.SET:
					case Transition.NOT_SET:
					case Transition.WILDCARD:
						continue;

					default:
						throw new IllegalStateException();
					}
				}
				// end debug check
			}
		}

		if (!canContinue) {
			return ParserProgress.COMPLETE;
		}

		if (changed) {
			return ParserProgress.EPSILON;
		}

		if (!hasUnfinishedRuleStopState) {
			return ParserProgress.NEXT_SYMBOL;
		}

		// step out of rule stop states, combining as necessary
		while (true) {
			int relevant = 0;
			int maxDepth = 0;
			int minDepth = Integer.MAX_VALUE;
			for (ParserState<?> state : _states) {
				if (!(state._state instanceof RuleStopState)) {
					continue;
				}

				relevant++;
				maxDepth = Math.max(maxDepth, state._depth);
				minDepth = Math.min(minDepth, state._depth);
			}

			if (relevant == 0) {
				break;
			}

			MultiMap<PredictionContext, ParserState<Symbol>> statesToProcess = new MultiMap<PredictionContext, ParserState<Symbol>>();
			int j = 0;
			for (int i = 0; i < _states.size(); i++) {
				if (_states.get(i)._depth == maxDepth && _states.get(i)._state instanceof RuleStopState) {
					statesToProcess.map(_states.get(i)._context, _states.get(i));
					continue;
				}

				if (j < i) {
					_states.set(j, _states.get(i));
				}

				j++;
			}

			_states.subList(j, _states.size()).clear();

			// items with the same return state context can be combined
			for (Map.Entry<PredictionContext, List<ParserState<Symbol>>> entry : statesToProcess.entrySet()) {
				List<ParserState<Symbol>> states = entry.getValue();

				PredictionContext mergedTrace = states.get(0)._trace;
				for (int i = 1; i < states.size(); i++) {
					mergedTrace = PredictionContextCache.UNCACHED.join(mergedTrace, states.get(i)._trace);
				}

				if (states.get(0)._context.size() != 1) {
					throw new UnsupportedOperationException("Not yet implemented.");
				}

				ATNState returnState = getATN().states.get(states.get(0)._context.getReturnState(0));
				_states.add(new ParserState<Symbol>(returnState, states.get(0)._context.getParent(0), mergedTrace, states.get(0)._depth - 1));
			}
		}

		return ParserProgress.EPSILON;
	}

	private BigInteger getTreeCount(PredictionContext trace) {
		return getTreeCount(trace, new IdentityHashMap<BigInteger>());
	}

	private BigInteger getTreeCount(PredictionContext trace, IdentityHashMap<BigInteger> visited) {
		while (trace.size() == 1) {
			trace = trace.getParent(0);
		}

		if (trace.isEmpty()) {
			return BigInteger.ONE;
		}

		BigInteger result = visited.get(trace);
		if (result == null) {
			result = BigInteger.ZERO;
			for (int i = 0; i < trace.size(); i++) {
				result = result.add(getTreeCount(trace.getParent(i), visited));
			}

			visited.put(trace, result);
		}

		return result;
	}

	protected enum ParserProgress {
		NEXT_SYMBOL,
		EPSILON,
		COMPLETE,
	}

	protected static class ParserState<Symbol extends Token> {
		private final ATNState _state;
		private final PredictionContext _context;
		private final PredictionContext _trace;
		private final int _depth;

		public ParserState(@NotNull ATNState state, @NotNull PredictionContext context, @NotNull PredictionContext trace, int depth) {
			this._state = state;
			this._context = context;
			this._trace = trace;
			this._depth = depth;
		}
	}
}
