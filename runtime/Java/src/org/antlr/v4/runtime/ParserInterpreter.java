/*
 * [The "BSD license"]
 * Copyright (c) 2013 Terence Parr
 * Copyright (c) 2013 Sam Harwell
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. The name of the author may not be used to endorse or promote products
 *    derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package org.antlr.v4.runtime;

import org.antlr.v4.runtime.atn.ATN;
import org.antlr.v4.runtime.atn.ATNState;
import org.antlr.v4.runtime.atn.ActionTransition;
import org.antlr.v4.runtime.atn.AtomTransition;
import org.antlr.v4.runtime.atn.DecisionState;
import org.antlr.v4.runtime.atn.LoopEndState;
import org.antlr.v4.runtime.atn.ParserATNSimulator;
import org.antlr.v4.runtime.atn.PrecedencePredicateTransition;
import org.antlr.v4.runtime.atn.PredicateTransition;
import org.antlr.v4.runtime.atn.RuleStartState;
import org.antlr.v4.runtime.atn.RuleTransition;
import org.antlr.v4.runtime.atn.StarLoopEntryState;
import org.antlr.v4.runtime.atn.Transition;
import org.antlr.v4.runtime.misc.NotNull;
import org.antlr.v4.runtime.misc.Tuple;
import org.antlr.v4.runtime.misc.Tuple2;

import java.util.ArrayDeque;
import java.util.BitSet;
import java.util.Collection;
import java.util.Deque;

/** A parser simulator that mimics what ANTLR's generated
 *  parser code does. A ParserATNSimulator is used to make
 *  predictions via adaptivePredict but this class moves a pointer through the
 *  ATN to simulate parsing. ParserATNSimulator just
 *  makes us efficient rather than having to backtrack, for example.
 *
 *  This properly creates parse trees even for left recursive rules.
 *
 *  We rely on the left recursive rule invocation and special predicate
 *  transitions to make left recursive rules work.
 *
 *  See TestParserInterpreter for examples.
 */
public class ParserInterpreter extends Parser {
	protected final String grammarFileName;
	protected final ATN atn;
	/** This identifies StarLoopEntryState's that begin the (...)*
	 *  precedence loops of left recursive rules.
	 */
	protected final BitSet pushRecursionContextStates;

	@Deprecated
	protected final String[] tokenNames;
	protected final String[] ruleNames;
	@NotNull
	private final Vocabulary vocabulary;

	/** Tracks LR rules for adjusting the contexts */
	protected final Deque<Tuple2<ParserRuleContext, Integer>> _parentContextStack =
		new ArrayDeque<Tuple2<ParserRuleContext, Integer>>();

	/** We need a map from (decision,inputIndex)->forced alt for computing ambiguous
	 *  parse trees. For now, we allow exactly one override.
	 */
	protected int overrideDecision = -1;
	protected int overrideDecisionInputIndex = -1;
	protected int overrideDecisionAlt = -1;

	/** A copy constructor that creates a new parser interpreter by reusing
	 *  the fields of a previous interpreter.
	 *
	 *  @param old The interpreter to copy
	 *
	 *  @since 4.5
	 */
	public ParserInterpreter(@NotNull ParserInterpreter old) {
		super(old.getInputStream());
		this.grammarFileName = old.grammarFileName;
		this.atn = old.atn;
		this.pushRecursionContextStates = old.pushRecursionContextStates;
		this.tokenNames = old.tokenNames;
		this.ruleNames = old.ruleNames;
		this.vocabulary = old.vocabulary;
		setInterpreter(new ParserATNSimulator(this, atn));
	}

	/**
	 * @deprecated Use {@link #ParserInterpreter(String, Vocabulary, Collection, ATN, TokenStream)} instead.
	 */
	@Deprecated
	public ParserInterpreter(String grammarFileName, Collection<String> tokenNames,
							 Collection<String> ruleNames, ATN atn, TokenStream input) {
		this(grammarFileName, VocabularyImpl.fromTokenNames(tokenNames.toArray(new String[tokenNames.size()])), ruleNames, atn, input);
	}

	public ParserInterpreter(String grammarFileName, @NotNull Vocabulary vocabulary,
							 Collection<String> ruleNames, ATN atn, TokenStream input)
	{
		super(input);
		this.grammarFileName = grammarFileName;
		this.atn = atn;
		this.tokenNames = new String[atn.maxTokenType];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = vocabulary.getDisplayName(i);
		}

		this.ruleNames = ruleNames.toArray(new String[ruleNames.size()]);
		this.vocabulary = vocabulary;

		// identify the ATN states where pushNewRecursionContext() must be called
		this.pushRecursionContextStates = new BitSet(atn.states.size());
		for (ATNState state : atn.states) {
			if (!(state instanceof StarLoopEntryState)) {
				continue;
			}

			if (((StarLoopEntryState)state).precedenceRuleDecision) {
				this.pushRecursionContextStates.set(state.stateNumber);
			}
		}

		// get atn simulator that knows how to do predictions
		setInterpreter(new ParserATNSimulator(this, atn));
	}

	@Override
	public ATN getATN() {
		return atn;
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override
	public Vocabulary getVocabulary() {
		return vocabulary;
	}

	@Override
	public String[] getRuleNames() {
		return ruleNames;
	}

	@Override
	public String getGrammarFileName() {
		return grammarFileName;
	}

	/** Begin parsing at startRuleIndex */
	public ParserRuleContext parse(int startRuleIndex) {
		RuleStartState startRuleStartState = atn.ruleToStartState[startRuleIndex];

		InterpreterRuleContext rootContext = new InterpreterRuleContext(null, ATNState.INVALID_STATE_NUMBER, startRuleIndex);
		if (startRuleStartState.isPrecedenceRule) {
			enterRecursionRule(rootContext, startRuleStartState.stateNumber, startRuleIndex, 0);
		}
		else {
			enterRule(rootContext, startRuleStartState.stateNumber, startRuleIndex);
		}

		while ( true ) {
			ATNState p = getATNState();
			switch ( p.getStateType() ) {
			case RULE_STOP :
				// pop; return from rule
				if ( _ctx.isEmpty() ) {
					if (startRuleStartState.isPrecedenceRule) {
						ParserRuleContext result = _ctx;
						Tuple2<ParserRuleContext, Integer> parentContext = _parentContextStack.pop();
						unrollRecursionContexts(parentContext.getItem1());
						return result;
					}
					else {
						exitRule();
						return rootContext;
					}
				}

				visitRuleStopState(p);
				break;

			default :
				try {
					visitState(p);
				}
				catch (RecognitionException e) {
					setState(atn.ruleToStopState[p.ruleIndex].stateNumber);
					getContext().exception = e;
					getErrorHandler().reportError(this, e);
					getErrorHandler().recover(this, e);
				}

				break;
			}
		}
	}

	@Override
	public void enterRecursionRule(ParserRuleContext localctx, int state, int ruleIndex, int precedence) {
		_parentContextStack.push(Tuple.create(_ctx, localctx.invokingState));
		super.enterRecursionRule(localctx, state, ruleIndex, precedence);
	}

	/**
	 * @sharpen.property AtnState
	 */
	protected ATNState getATNState() {
		return atn.states.get(getState());
	}

	protected void visitState(ATNState p) {
		int edge;
		if (p.getNumberOfTransitions() > 1) {
			getErrorHandler().sync(this);
			int decision = ((DecisionState) p).decision;
			if ( decision == overrideDecision && _input.index() == overrideDecisionInputIndex ) {
				edge = overrideDecisionAlt;
			}
			else {
				edge = getInterpreter().adaptivePredict(_input, decision, _ctx);
			}
		}
		else {
			edge = 1;
		}

		Transition transition = p.transition(edge - 1);
		switch (transition.getSerializationType()) {
		case EPSILON:
			if ( pushRecursionContextStates.get(p.stateNumber) &&
				 !(transition.target instanceof LoopEndState))
			{
				// We are at the start of a left recursive rule's (...)* loop
				// but it's not the exit branch of loop.
				InterpreterRuleContext ctx = new InterpreterRuleContext(_parentContextStack.peek().getItem1(), _parentContextStack.peek().getItem2(), _ctx.getRuleIndex());
				pushNewRecursionContext(ctx, atn.ruleToStartState[p.ruleIndex].stateNumber, _ctx.getRuleIndex());
			}
			break;

		case ATOM:
			match(((AtomTransition)transition).label);
			break;

		case RANGE:
		case SET:
		case NOT_SET:
			if (!transition.matches(_input.LA(1), Token.MIN_USER_TOKEN_TYPE, 65535)) {
				_errHandler.recoverInline(this);
			}
			matchWildcard();
			break;

		case WILDCARD:
			matchWildcard();
			break;

		case RULE:
			RuleStartState ruleStartState = (RuleStartState)transition.target;
			int ruleIndex = ruleStartState.ruleIndex;
			InterpreterRuleContext ctx = new InterpreterRuleContext(_ctx, p.stateNumber, ruleIndex);
			if (ruleStartState.isPrecedenceRule) {
				enterRecursionRule(ctx, ruleStartState.stateNumber, ruleIndex, ((RuleTransition)transition).precedence);
			}
			else {
				enterRule(ctx, transition.target.stateNumber, ruleIndex);
			}
			break;

		case PREDICATE:
			PredicateTransition predicateTransition = (PredicateTransition)transition;
			if (!sempred(_ctx, predicateTransition.ruleIndex, predicateTransition.predIndex)) {
				throw new FailedPredicateException(this);
			}

			break;

		case ACTION:
			ActionTransition actionTransition = (ActionTransition)transition;
			action(_ctx, actionTransition.ruleIndex, actionTransition.actionIndex);
			break;

		case PRECEDENCE:
			if (!precpred(_ctx, ((PrecedencePredicateTransition)transition).precedence)) {
				throw new FailedPredicateException(this, String.format("precpred(_ctx, %d)", ((PrecedencePredicateTransition)transition).precedence));
			}
			break;

		default:
			throw new UnsupportedOperationException("Unrecognized ATN transition type.");
		}

		setState(transition.target.stateNumber);
	}

	protected void visitRuleStopState(ATNState p) {
		RuleStartState ruleStartState = atn.ruleToStartState[p.ruleIndex];
		if (ruleStartState.isPrecedenceRule) {
			Tuple2<ParserRuleContext, Integer> parentContext = _parentContextStack.pop();
			unrollRecursionContexts(parentContext.getItem1());
			setState(parentContext.getItem2());
		}
		else {
			exitRule();
		}

		RuleTransition ruleTransition = (RuleTransition)atn.states.get(getState()).transition(0);
		setState(ruleTransition.followState.stateNumber);
	}

	/** Override this parser interpreters normal decision-making process
	 *  at a particular decision and input token index. Instead of
	 *  allowing the adaptive prediction mechanism to choose the
	 *  first alternative within a block that leads to a successful parse,
	 *  force it to take the alternative, 1..n for n alternatives.
	 *
	 *  As an implementation limitation right now, you can only specify one
	 *  override. This is sufficient to allow construction of different
	 *  parse trees for ambiguous input. It means re-parsing the entire input
	 *  in general because you're never sure where an ambiguous sequence would
	 *  live in the various parse trees. For example, in one interpretation,
	 *  an ambiguous input sequence would be matched completely in expression
	 *  but in another it could match all the way back to the root.
	 *
	 *  s : e '!'? ;
	 *  e : ID
	 *    | ID '!'
	 *    ;
	 *
	 *  Here, x! can be matched as (s (e ID) !) or (s (e ID !)). In the first
	 *  case, the ambiguous sequence is fully contained only by the root.
	 *  In the second case, the ambiguous sequences fully contained within just
	 *  e, as in: (e ID !).
	 *
	 *  Rather than trying to optimize this and make
	 *  some intelligent decisions for optimization purposes, I settled on
	 *  just re-parsing the whole input and then using
	 *  {link Trees#getRootOfSubtreeEnclosingRegion} to find the minimal
	 *  subtree that contains the ambiguous sequence. I originally tried to
	 *  record the call stack at the point the parser detected and ambiguity but
	 *  left recursive rules create a parse tree stack that does not reflect
	 *  the actual call stack. That impedance mismatch was enough to make
	 *  it it challenging to restart the parser at a deeply nested rule
	 *  invocation.
	 *
	 *  Only parser interpreters can override decisions so as to avoid inserting
	 *  override checking code in the critical ALL(*) prediction execution path.
	 *
	 *  @since 4.5
	 */
	public void addDecisionOverride(int decision, int tokenIndex, int forcedAlt) {
		overrideDecision = decision;
		overrideDecisionInputIndex = tokenIndex;
		overrideDecisionAlt = forcedAlt;
	}
}
