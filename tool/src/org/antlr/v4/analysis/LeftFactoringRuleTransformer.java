/*
 * [The "BSD license"]
 *  Copyright (c) 2012 Sam Harwell
 *  All rights reserved.
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions
 *  are met:
 *  1. Redistributions of source code must retain the above copyright
 *      notice, this list of conditions and the following disclaimer.
 *  2. Redistributions in binary form must reproduce the above copyright
 *      notice, this list of conditions and the following disclaimer in the
 *      documentation and/or other materials provided with the distribution.
 *  3. The name of the author may not be used to endorse or promote products
 *      derived from this software without specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 *  IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 *  OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 *  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 *  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 *  NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 *  THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
package org.antlr.v4.analysis;

import org.antlr.v4.Tool;
import org.antlr.v4.parse.ANTLRParser;
import org.antlr.v4.parse.GrammarASTAdaptor;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.atn.ATNSimulator;
import org.antlr.v4.runtime.misc.IntervalSet;
import org.antlr.v4.runtime.misc.NotNull;
import org.antlr.v4.runtime.misc.Tuple;
import org.antlr.v4.runtime.misc.Tuple2;
import org.antlr.v4.tool.Alternative;
import org.antlr.v4.tool.ErrorType;
import org.antlr.v4.tool.Grammar;
import org.antlr.v4.tool.LeftRecursiveRule;
import org.antlr.v4.tool.Rule;
import org.antlr.v4.tool.ast.ActionAST;
import org.antlr.v4.tool.ast.AltAST;
import org.antlr.v4.tool.ast.BlockAST;
import org.antlr.v4.tool.ast.GrammarAST;
import org.antlr.v4.tool.ast.GrammarRootAST;
import org.antlr.v4.tool.ast.PlusBlockAST;
import org.antlr.v4.tool.ast.RuleAST;
import org.antlr.v4.tool.ast.RuleRefAST;
import org.antlr.v4.tool.ast.StarBlockAST;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * This class implements automatic left-factoring for rules in a grammar. This
 * class supports indirect left recursion removal by allowing a rule to be
 * left-factored out of itself.
 *
 * @author Sam Harwell
 */
public class LeftFactoringRuleTransformer {
	/**
	 * This option can be added to a grammar rule to force a rule to be
	 * automatically left-factored by this transformation.
	 */
	public static final String LEFTFACTOR = "leftfactor";

	private static final Logger LOGGER = Logger.getLogger(LeftFactoringRuleTransformer.class.getName());

	/**
	 * The {@link Grammar} to process.
	 */
	public final Grammar _g;

	/**
	 * This map tracks the variants which are created for rules in the grammar
	 * throughout the left-factoring process. The keys of the map are pairs; the
	 * first item is the name of the target rule of the left-factoring
	 * operation, and the second item is the name of the rule which is being
	 * left-factored out of the target rule. The values of the map are a
	 * {@link RuleVariants} instance indicating the net result of the specific
	 * left-factoring operation described by the key.
	 */
	private final Map<Tuple2<String, String>, RuleVariants> _variants = new HashMap<Tuple2<String, String>, RuleVariants>();

	/**
	 * This {@link GrammarASTAdaptor} is used for manipulating the AST for rules
	 * in the grammar during the left-factoring process.
	 */
	private final GrammarASTAdaptor adaptor = new GrammarASTAdaptor();

	public LeftFactoringRuleTransformer(@NotNull Grammar g) {
		this._g = g;
	}

	/**
	 * Perform automatic left-factoring on all rules in the grammar that require
	 * it. This method first removes all remaining left-recursion from the
	 * grammar, following by left-factoring rules that were explicitly marked
	 * with the {@code @leftfactor{}} named action.
	 */
	public void translateLeftFactoredRules() {
		// first translate to remove left recursion
		translateIndirectLeftRecursion();
		// second translate to handle the @leftfactor named action
		translateExplicitLeftFactoredRules();
	}

	/**
	 * Remove left-recursion from the grammar by iteratively removing
	 * left-recursion from individual rules until no more left-recursive rules
	 * exist in the grammar.
	 */
	protected void translateIndirectLeftRecursion() {
		boolean changed;
		do {
			changed = false;
			List<Rule> rules = new ArrayList<Rule>(_g.rules.values());
			for (Rule r : rules) {
				if (Grammar.isTokenName(r.name)) {
					continue;
				}

				changed |= translateIndirectLeftRecursion(r);
			}
		} while (changed);
	}

	/**
	 * Remove left-recursion from rule {@code r} by applying the left-factoring
	 * transformation to itself.
	 *
	 * @param r The rule to remove left recursion from.
	 * @return {@code true} if changes were made to {@code r}; otherwise,
	 * {@code false} if no changes were required (i.e. rule {@code r} was not
	 * directly or indirectly left-recursive).
	 */
	protected boolean translateIndirectLeftRecursion(Rule r) {
		if (_variants.containsKey(Tuple.create(r.name, r.name))) {
			return false;
		}

		LOGGER.log(Level.FINE, "Left factoring {0} out of alts in grammar rule {1}", new Object[] { r.name, r.name });

		GrammarAST block = (GrammarAST)r.ast.getFirstChildWithType(ANTLRParser.BLOCK);

		RuleVariants ruleVariants = createLeftFactoredRuleVariant(r, r.name);
		switch (ruleVariants) {
		case NONE:
			// no left recursion from this rule
			return false;

		case PARTIALLY_FACTORED:
			/* Replace the existing rule r with
			 *
			 * r$nolf$r (r$lf$r)*
			 */
			GrammarAST root = adaptor.nil();
			AltAST newAlt = new AltAST(adaptor.createToken(ANTLRParser.ALT, "ALT"));
			adaptor.addChild(root, newAlt);

			String unfactoredRule = r.name + ATNSimulator.RULE_NOLF_VARIANT_MARKER + r.name;
			Rule unfactoredRuleDef = _g.getRule(unfactoredRule);
			adaptor.addChild(newAlt, adaptor.dupTree(unfactoredRuleDef.ast.getFirstChildWithType(ANTLRParser.BLOCK)));

			String factoredRule = r.name + ATNSimulator.RULE_LF_VARIANT_MARKER + r.name;
			Rule factoredRuleDef = _g.getRule(factoredRule);
			StarBlockAST closure = new StarBlockAST(ANTLRParser.CLOSURE, adaptor.createToken(ANTLRParser.CLOSURE, "CLOSURE"), null);
			closure.setOption("pushRecursionContext", adaptor.create(ANTLRParser.ID, factoredRuleDef.getBaseContext()));
			adaptor.addChild(closure, adaptor.dupTree(factoredRuleDef.ast.getFirstChildWithType(ANTLRParser.BLOCK)));
			adaptor.addChild(newAlt, closure);

			block.replaceChildren(0, block.getChildCount() - 1, root);

			if (block.getParent() instanceof RuleAST) {
				r.numberOfAlts = 1;
				r.alt = new Alternative[2];
				r.alt[1] = new Alternative(r, 1);
				r.alt[1].ast = newAlt;
			}

			if (_g.undefineRule(unfactoredRuleDef)) {
				GrammarAST ruleParent = (GrammarAST)unfactoredRuleDef.ast.getParent();
				ruleParent.deleteChild(unfactoredRuleDef.ast.getChildIndex());
				ruleParent.freshenParentAndChildIndexes(unfactoredRuleDef.ast.getChildIndex());
			}

			if (_g.undefineRule(factoredRuleDef)) {
				GrammarAST ruleParent = (GrammarAST)factoredRuleDef.ast.getParent();
				ruleParent.deleteChild(factoredRuleDef.ast.getChildIndex());
				ruleParent.freshenParentAndChildIndexes(factoredRuleDef.ast.getChildIndex());
			}

			return true;

		case FULLY_FACTORED:
			_g.tool.errMgr.grammarError(ErrorType.NO_NON_LR_ALTS, _g.fileName, adaptor.getToken(r.ast.getChild(0)), r.name);
			return false;

		case PROCESSING:
		default:
			throw new UnsupportedOperationException("unknown rule variants");
		}
	}

	protected void translateExplicitLeftFactoredRules() {
		// translate all rules marked for auto left factoring
		List<Rule> rulesToProcess = new ArrayList<Rule>(_g.rules.values());
		for (Rule r : rulesToProcess) {
			if (Grammar.isTokenName(r.name)) {
				continue;
			}

			Object leftFactoredRulesAction = r.namedActions.get(LEFTFACTOR);
			if (!(leftFactoredRulesAction instanceof ActionAST)) {
				continue;
			}

			String leftFactoredRuleAction = leftFactoredRulesAction.toString();
			leftFactoredRuleAction = leftFactoredRuleAction.substring(1, leftFactoredRuleAction.length() - 1);
			String[] rules = leftFactoredRuleAction.split(",\\s*");
			List<String> leftFactoredRules = Arrays.asList(rules);

			LOGGER.log(Level.FINE, "Left factoring {0} out of alts in grammar rule {1}", new Object[] { leftFactoredRules, r.name });

			Set<GrammarAST> translatedBlocks = new HashSet<GrammarAST>();
			List<GrammarAST> blocks = r.ast.getNodesWithType(ANTLRParser.BLOCK);
			blockLoop:
			for (GrammarAST block : blocks) {
				for (GrammarAST current = (GrammarAST)block.getParent(); current != null; current = (GrammarAST)current.getAncestor(ANTLRParser.BLOCK)) {
					if (translatedBlocks.contains(current)) {
						// an enclosing decision was already factored
						continue blockLoop;
					}
				}

				for (String rule : leftFactoredRules) {
					if (translatedBlocks.contains(block)) {
						throw new UnsupportedOperationException("Chained left factoring is not yet implemented.");
					}

					try {
						if (!translateLeftFactoredDecision(block, rule, false, DecisionFactorMode.COMBINED_FACTOR, true)) {
							// couldn't translate the decision
							continue;
						}

						translatedBlocks.add(block);
					}
					catch (IllegalStateException ex) {
						// recursive call detected
					}
				}
			}
		}
	}

	protected boolean expandOptionalQuantifiersForBlock(GrammarAST block, boolean variant) {
		List<GrammarAST> children = new ArrayList<GrammarAST>();
		for (int i = 0; i < block.getChildCount(); i++) {
			GrammarAST child = (GrammarAST)block.getChild(i);
			if (child.getType() != ANTLRParser.ALT) {
				children.add(child);
				continue;
			}

			GrammarAST expandedAlt = expandOptionalQuantifiersForAlt(child);
			if (expandedAlt == null) {
				return false;
			}

			children.add(expandedAlt);
		}

		GrammarAST newChildren = adaptor.nil();
		newChildren.addChildren(children);
		block.replaceChildren(0, block.getChildCount() - 1, newChildren);
		block.freshenParentAndChildIndexesDeeply();

		if (!variant && block.getParent() instanceof RuleAST) {
			RuleAST ruleAST = (RuleAST)block.getParent();
			String ruleName = ruleAST.getChild(0).getText();
			Rule r = _g.getRule(ruleName);
			List<GrammarAST> blockAlts = block.getAllChildrenWithType(ANTLRParser.ALT);
			r.numberOfAlts = blockAlts.size();
			r.alt = new Alternative[blockAlts.size() + 1];
			for (int i = 0; i < blockAlts.size(); i++) {
				r.alt[i + 1] = new Alternative(r, i + 1);
				r.alt[i + 1].ast = (AltAST)blockAlts.get(i);
			}
		}

		return true;
	}

	protected GrammarAST expandOptionalQuantifiersForAlt(GrammarAST alt) {
		if (alt.getChildCount() == 0) {
			return null;
		}

		if (alt.getChild(0).getType() == ANTLRParser.OPTIONAL) {
			GrammarAST root = adaptor.nil();

			GrammarAST alt2 = alt.dupTree();
			alt2.deleteChild(0);
			if (alt2.getChildCount() == 0) {
				adaptor.addChild(alt2, adaptor.create(ANTLRParser.EPSILON, "EPSILON"));
			}

			alt.setChild(0, alt.getChild(0).getChild(0));
			if (alt.getChild(0).getType() == ANTLRParser.BLOCK && alt.getChild(0).getChildCount() == 1 && alt.getChild(0).getChild(0).getType() == ANTLRParser.ALT) {
				GrammarAST list = adaptor.nil();
				for (Object tree : ((GrammarAST)alt.getChild(0).getChild(0)).getChildren()) {
					adaptor.addChild(list, tree);
				}

				adaptor.replaceChildren(alt, 0, 0, list);
			}

			adaptor.addChild(root, alt);
			adaptor.addChild(root, alt2);
			return root;
		}
		else if (alt.getChild(0).getType() == ANTLRParser.CLOSURE) {
			GrammarAST root = adaptor.nil();

			GrammarAST alt2 = alt.dupTree();
			alt2.deleteChild(0);
			if (alt2.getChildCount() == 0) {
				adaptor.addChild(alt2, adaptor.create(ANTLRParser.EPSILON, "EPSILON"));
			}

			PlusBlockAST plusBlockAST = new PlusBlockAST(ANTLRParser.POSITIVE_CLOSURE, adaptor.createToken(ANTLRParser.POSITIVE_CLOSURE, "+"), null);
			for (int i = 0; i < alt.getChild(0).getChildCount(); i++) {
				plusBlockAST.addChild(alt.getChild(0).getChild(i));
			}

			alt.setChild(0, plusBlockAST);

			adaptor.addChild(root, alt);
			adaptor.addChild(root, alt2);
			return root;
		}

		return alt;
	}

	protected boolean translateLeftFactoredDecision(GrammarAST block, String factoredRule, boolean variant, DecisionFactorMode mode, boolean includeFactoredElement) {
		if (mode == DecisionFactorMode.PARTIAL_UNFACTORED && includeFactoredElement) {
			throw new IllegalArgumentException("Cannot include the factored element in unfactored alternatives.");
		}
		else if (mode == DecisionFactorMode.COMBINED_FACTOR && !includeFactoredElement) {
			throw new IllegalArgumentException("Cannot return a combined answer without the factored element.");
		}

		if (!expandOptionalQuantifiersForBlock(block, variant)) {
			return false;
		}

		List<GrammarAST> alternatives = block.getAllChildrenWithType(ANTLRParser.ALT);
		GrammarAST[] factoredAlternatives = new GrammarAST[alternatives.size()];
		GrammarAST[] unfactoredAlternatives = new GrammarAST[alternatives.size()];
		IntervalSet factoredIntervals = new IntervalSet();
		IntervalSet unfactoredIntervals = new IntervalSet();
		for (int i = 0; i < alternatives.size(); i++) {
			GrammarAST alternative = alternatives.get(i);
			if (mode.includeUnfactoredAlts() || mode == DecisionFactorMode.FULL_FACTOR) {
				GrammarAST unfactoredAlt = alternative.dupTree();
				unfactoredAlt.parent = alternative.parent;
				unfactoredAlt = translateLeftFactoredAlternative(unfactoredAlt, factoredRule, variant, DecisionFactorMode.PARTIAL_UNFACTORED, false);
				unfactoredAlternatives[i] = unfactoredAlt;
				if (unfactoredAlt != null) {
					unfactoredIntervals.add(i);
				}
			}

			if (mode.includeFactoredAlts()) {
				GrammarAST factoredAlt = translateLeftFactoredAlternative(alternative, factoredRule, variant, mode == DecisionFactorMode.COMBINED_FACTOR ? DecisionFactorMode.PARTIAL_FACTORED : mode, includeFactoredElement);
				factoredAlternatives[i] = factoredAlt;
				if (factoredAlt != null) {
					factoredIntervals.add(alternative.getChildIndex());
				}
			}
		}

		if (factoredIntervals.isNil() && !mode.includeUnfactoredAlts()) {
			return false;
		} else if (unfactoredIntervals.isNil() && !mode.includeFactoredAlts()) {
			return false;
		}

		if (unfactoredIntervals.isNil() && factoredIntervals.size() == alternatives.size() && mode.includeFactoredAlts() && !includeFactoredElement) {
			for (int i = 0; i < factoredAlternatives.length; i++) {
				GrammarAST translatedAlt = factoredAlternatives[i];
				if (translatedAlt.getChildCount() == 0) {
					adaptor.addChild(translatedAlt, adaptor.create(ANTLRParser.EPSILON, "EPSILON"));
				}

				adaptor.setChild(block, i, translatedAlt);
			}

			return true;
		}
		else if (factoredIntervals.isNil() && unfactoredIntervals.size() == alternatives.size() && mode.includeUnfactoredAlts()) {
			for (int i = 0; i < unfactoredAlternatives.length; i++) {
				GrammarAST translatedAlt = unfactoredAlternatives[i];
				if (translatedAlt.getChildCount() == 0) {
					adaptor.addChild(translatedAlt, adaptor.create(ANTLRParser.EPSILON, "EPSILON"));
				}

				adaptor.setChild(block, i, translatedAlt);
			}

			return true;
		}

		if (mode == DecisionFactorMode.FULL_FACTOR) {
			return false;
		}

		/* for a, b, c being arbitrary `element` trees, this block performs
		 * this transformation:
		 *
		 * factoredElement a
		 * | factoredElement b
		 * | factoredElement c
		 * | ...
		 *
		 * ==>
		 *
		 * factoredElement (a | b | c | ...)
		 */
		GrammarAST newChildren = adaptor.nil();
		for (int i = 0; i < alternatives.size(); i++) {
			if (mode.includeFactoredAlts() && factoredIntervals.contains(i)) {
				boolean combineWithPrevious = i > 0 && factoredIntervals.contains(i - 1) && (!mode.includeUnfactoredAlts() || !unfactoredIntervals.contains(i - 1));
				if (combineWithPrevious) {
					GrammarAST translatedAlt = factoredAlternatives[i];
					if (translatedAlt.getChildCount() == 0) {
						adaptor.addChild(translatedAlt, adaptor.create(ANTLRParser.EPSILON, "EPSILON"));
					}

					GrammarAST previous = (GrammarAST)newChildren.getChild(newChildren.getChildCount() - 1);
					if (LOGGER.isLoggable(Level.FINE)) {
						LOGGER.log(Level.FINE, previous.toStringTree());
						LOGGER.log(Level.FINE, translatedAlt.toStringTree());
					}
					if (previous.getChildCount() == 1 || previous.getChild(1).getType() != ANTLRParser.BLOCK) {
						GrammarAST newBlock = new BlockAST(adaptor.createToken(ANTLRParser.BLOCK, "BLOCK"));
						GrammarAST newAlt = new AltAST(adaptor.createToken(ANTLRParser.ALT, "ALT"));
						adaptor.addChild(newBlock, newAlt);
						while (previous.getChildCount() > 0) {
							adaptor.addChild(newAlt, previous.deleteChild(0));
						}

						if (newAlt.getChildCount() == 0) {
							adaptor.addChild(newAlt, adaptor.create(ANTLRParser.EPSILON, "EPSILON"));
						}

						adaptor.addChild(previous, newBlock);
					}

					if (translatedAlt.getChildCount() == 1 || translatedAlt.getChild(1).getType() != ANTLRParser.BLOCK) {
						GrammarAST newBlock = new BlockAST(adaptor.createToken(ANTLRParser.BLOCK, "BLOCK"));
						GrammarAST newAlt = new AltAST(adaptor.createToken(ANTLRParser.ALT, "ALT"));
						adaptor.addChild(newBlock, newAlt);
						while (translatedAlt.getChildCount() > 0) {
							adaptor.addChild(newAlt, translatedAlt.deleteChild(0));
						}

						if (newAlt.getChildCount() == 0) {
							adaptor.addChild(newAlt, adaptor.create(ANTLRParser.EPSILON, "EPSILON"));
						}

						adaptor.addChild(translatedAlt, newBlock);
					}

					GrammarAST combinedBlock = (GrammarAST)previous.getChild(0);
					adaptor.addChild(combinedBlock, translatedAlt.getChild(0).getChild(0));

					if (LOGGER.isLoggable(Level.FINE)) {
						LOGGER.log(Level.FINE, previous.toStringTree());
					}
				}
				else {
					GrammarAST translatedAlt = factoredAlternatives[i];
					if (translatedAlt.getChildCount() == 0) {
						adaptor.addChild(translatedAlt, adaptor.create(ANTLRParser.EPSILON, "EPSILON"));
					}

					adaptor.addChild(newChildren, translatedAlt);
				}
			}

			if (mode.includeUnfactoredAlts() && unfactoredIntervals.contains(i)) {
				GrammarAST translatedAlt = unfactoredAlternatives[i];
				if (translatedAlt.getChildCount() == 0) {
					adaptor.addChild(translatedAlt, adaptor.create(ANTLRParser.EPSILON, "EPSILON"));
				}

				adaptor.addChild(newChildren, translatedAlt);
			}
		}

		if (newChildren.isNil() && newChildren.getChildren() == null) {
			throw new IllegalStateException();
		}

		adaptor.replaceChildren(block, 0, block.getChildCount() - 1, newChildren);

		if (!variant && block.getParent() instanceof RuleAST) {
			RuleAST ruleAST = (RuleAST)block.getParent();
			String ruleName = ruleAST.getChild(0).getText();
			Rule r = _g.getRule(ruleName);
			List<GrammarAST> blockAlts = block.getAllChildrenWithType(ANTLRParser.ALT);
			r.numberOfAlts = blockAlts.size();
			r.alt = new Alternative[blockAlts.size() + 1];
			for (int i = 0; i < blockAlts.size(); i++) {
				r.alt[i + 1] = new Alternative(r, i + 1);
				r.alt[i + 1].ast = (AltAST)blockAlts.get(i);
			}
		}

		return true;
	}

	protected GrammarAST translateLeftFactoredAlternative(GrammarAST alternative, String factoredRule, boolean variant, DecisionFactorMode mode, boolean includeFactoredElement) {
		if (mode == DecisionFactorMode.PARTIAL_UNFACTORED && includeFactoredElement) {
			throw new IllegalArgumentException("Cannot include the factored element in unfactored alternatives.");
		}
		else if (mode == DecisionFactorMode.COMBINED_FACTOR && !includeFactoredElement) {
			throw new IllegalArgumentException("Cannot return a combined answer without the factored element.");
		}

		assert alternative.getChildCount() > 0;

		if (alternative.getChild(0).getType() == ANTLRParser.EPSILON) {
			if (mode == DecisionFactorMode.PARTIAL_UNFACTORED) {
				return alternative;
			}

			return null;
		}

		GrammarAST translatedElement = translateLeftFactoredElement((GrammarAST)alternative.getChild(0), factoredRule, variant, mode, includeFactoredElement);
		if (translatedElement == null) {
			return null;
		}

		alternative.replaceChildren(0, 0, translatedElement);
		if (alternative.getChildCount() == 0) {
			adaptor.addChild(alternative, adaptor.create(ANTLRParser.EPSILON, "EPSILON"));
		}

		assert alternative.getChildCount() > 0;
		return alternative;
	}

	protected GrammarAST translateLeftFactoredElement(GrammarAST element, String factoredRule, boolean variant, DecisionFactorMode mode, boolean includeFactoredElement) {
		if (mode == DecisionFactorMode.PARTIAL_UNFACTORED && includeFactoredElement) {
			throw new IllegalArgumentException("Cannot include the factored element in unfactored alternatives.");
		}

		if (mode == DecisionFactorMode.COMBINED_FACTOR) {
			throw new UnsupportedOperationException("Cannot return a combined answer.");
		}

		assert !mode.includeFactoredAlts() || !mode.includeUnfactoredAlts();

		GrammarAST labeledAST = null;
		switch (element.getType()) {
		case ANTLRParser.ASSIGN:
		case ANTLRParser.PLUS_ASSIGN:
			labeledAST = element;
			element = (GrammarAST)element.getChild(1);
			break;

		default:
			break;
		}

		switch (element.getType()) {
		case ANTLRParser.ASSIGN:
		case ANTLRParser.PLUS_ASSIGN:
			throw new IllegalStateException("ANTLR doesn't allow labels nested inside labels.");

		case ANTLRParser.RULE_REF:
		{
			/* label=a
			 *
			 * ==>
			 *
			 * factoredElement a_factored         (for unlabeled)
			 * factoredElement label=a_factored   (for ASSIGN labeled)
			 * factoredElement label+=a_factored  (for PLUS_ASSIGN labeled)
			 */
			if (factoredRule.equals(element.getToken().getText())) {
				if (!mode.includeFactoredAlts()) {
					return null;
				}

				if (includeFactoredElement) {
					// this element is already left factored
					return labeledAST != null ? labeledAST : element;
				}

				GrammarAST root = adaptor.nil();
				root.addChild(adaptor.create(Token.EPSILON, "EPSILON"));
				root.deleteChild(0);
				return root;
			}

			Rule targetRule = _g.getRule(element.getToken().getText());
			if (targetRule == null) {
				return null;
			}

			RuleVariants ruleVariants = createLeftFactoredRuleVariant(targetRule, factoredRule);
			if (ruleVariants == RuleVariants.PROCESSING) {
				// this occurs when overlapping left-recursive chains appear in
				// the grammar. the result will end up as NONE or
				// PARTIALLY_FACTORED. figure that out here so we can process it
				// properly below.
				if (containsLeftEdgeCall(targetRule, factoredRule)) {
					ruleVariants = RuleVariants.PARTIALLY_FACTORED;
				}
				else {
					ruleVariants = RuleVariants.NONE;
				}
			}

			switch (ruleVariants) {
			case NONE:
				if (!mode.includeUnfactoredAlts()) {
					return null;
				}

				// just call the original rule (leave the element unchanged)
				return labeledAST != null ? labeledAST : element;

			case FULLY_FACTORED:
				if (!mode.includeFactoredAlts()) {
					return null;
				}

				break;

			case PARTIALLY_FACTORED:
				break;

			default:
				throw new IllegalStateException();
			}

			String marker = mode.includeFactoredAlts() ? ATNSimulator.RULE_LF_VARIANT_MARKER : ATNSimulator.RULE_NOLF_VARIANT_MARKER;
			element.setText(element.getText() + marker + factoredRule);

			GrammarAST root = adaptor.nil();

			if (includeFactoredElement) {
				assert mode.includeFactoredAlts();
				RuleRefAST factoredRuleRef = new RuleRefAST(adaptor.createToken(ANTLRParser.RULE_REF, factoredRule));
				Rule factoredRuleDef = _g.getRule(factoredRule);
				if (factoredRuleDef instanceof LeftRecursiveRule) {
					factoredRuleRef.setOption(LeftRecursiveRuleTransformer.PRECEDENCE_OPTION_NAME, adaptor.create(ANTLRParser.INT, "0"));
				}

				if (_g.getRule(factoredRule).args != null && _g.getRule(factoredRule).args.size() > 0) {
					throw new UnsupportedOperationException("Cannot left-factor rules with arguments yet.");
				}

				adaptor.addChild(root, factoredRuleRef);
			}

			adaptor.addChild(root, labeledAST != null ? labeledAST : element);

			return root;
		}

		case ANTLRParser.BLOCK:
		{
			if (labeledAST != null) {
				RuleAST ruleAST = (RuleAST)labeledAST.getAncestor(ANTLRParser.RULE);
				LOGGER.log(Level.WARNING, "Could not left factor ''{0}'' out of decision in rule ''{1}'': labeled rule references are not yet supported.",
					new Object[] { factoredRule, ruleAST.getChild(0).getText() });
				return null;
			}

			GrammarAST cloned = element.dupTree();
			if (!translateLeftFactoredDecision(cloned, factoredRule, variant, mode, includeFactoredElement)) {
				return null;
			}

			if (cloned.getChildCount() != 1) {
				// if the BLOCK has more than one ALT, keep it as a BLOCK
				return cloned;
			}

			// otherwise, remove the wrapping BLOCK; effectively converts `(x)`
			// to just `x`.
			GrammarAST root = adaptor.nil();
			for (int i = 0; i < cloned.getChild(0).getChildCount(); i++) {
				adaptor.addChild(root, cloned.getChild(0).getChild(i));
			}

			return root;
		}

		case ANTLRParser.POSITIVE_CLOSURE:
		{
			if (labeledAST != null) {
				RuleAST ruleAST = (RuleAST)labeledAST.getAncestor(ANTLRParser.RULE);
				LOGGER.log(Level.WARNING, "Could not left factor ''{0}'' out of decision in rule ''{1}'': labeled rule references are not yet supported.",
					new Object[] { factoredRule, ruleAST.getChild(0).getText() });
				return null;
			}

			/* a+
			 *
			 * =>
			 *
			 * factoredElement a_factored a*
			 */

			GrammarAST originalChildElement = (GrammarAST)element.getChild(0);
			GrammarAST translatedElement = translateLeftFactoredElement(originalChildElement.dupTree(), factoredRule, variant, mode, includeFactoredElement);
			if (translatedElement == null) {
				return null;
			}

			GrammarAST closure = new StarBlockAST(ANTLRParser.CLOSURE, adaptor.createToken(ANTLRParser.CLOSURE, "CLOSURE"), null);
			adaptor.addChild(closure, originalChildElement);

			GrammarAST root = adaptor.nil();
			if (mode.includeFactoredAlts()) {
				if (includeFactoredElement) {
					Object factoredElement = adaptor.deleteChild(translatedElement, 0);
					adaptor.addChild(root, factoredElement);
				}
			}
			adaptor.addChild(root, translatedElement);
			adaptor.addChild(root, closure);
			return root;
		}

		case ANTLRParser.CLOSURE:
		case ANTLRParser.OPTIONAL:
			// not yet supported
			if (mode.includeUnfactoredAlts()) {
				return labeledAST != null ? labeledAST : element;
			}

			return null;

		case ANTLRParser.DOT:
			// ref to imported grammar, not yet supported
			if (mode.includeUnfactoredAlts()) {
				return labeledAST != null ? labeledAST : element;
			}

			return null;

		case ANTLRParser.ACTION:
		case ANTLRParser.SEMPRED:
			if (mode.includeUnfactoredAlts()) {
				return labeledAST != null ? labeledAST : element;
			}

			return null;

		case ANTLRParser.WILDCARD:
		case ANTLRParser.STRING_LITERAL:
		case ANTLRParser.TOKEN_REF:
		case ANTLRParser.NOT:
		case ANTLRParser.SET:
			// terminals
			if (mode.includeUnfactoredAlts()) {
				return labeledAST != null ? labeledAST : element;
			}

			return null;

		case ANTLRParser.EPSILON:
			// empty tree
			if (mode.includeUnfactoredAlts()) {
				return labeledAST != null ? labeledAST : element;
			}

			return null;

		default:
			// unknown
			return null;
		}
	}

	private final Map<Tuple2<String, String>, Boolean> _knownCalls = new HashMap<Tuple2<String, String>, Boolean>();

	/**
	 * Determine if {@code rule} contains a left-edge call to rule
	 * {@code target}.
	 *
	 * @param rule The source rule to analyze.
	 * @param target The target rule to test for on the left edge of {@code rule}.
	 * @return {@code true} if {@code rule} contains a left-edge call to rule
	 * {@code target}; otherwise, {@code false}.
	 */
	protected final boolean containsLeftEdgeCall(@NotNull Rule rule, @NotNull String target) {
		Boolean result = _knownCalls.get(Tuple.create(rule.name, target));
		if (result != null) {
			return result;
		}

		LOGGER.log(Level.FINER, "Checking if rule {0} calls rule {1}...", new Object[] { rule.name, target });
		return containsLeftEdgeCall(rule.name, target, new HashSet<String>());
	}

	protected boolean containsLeftEdgeCall(@NotNull String rule, @NotNull String target, Set<String> visited) {
		Boolean result = _knownCalls.get(Tuple.create(rule, target));
		if (result != null) {
			return result;
		}

		if (!visited.add(rule)) {
			// if there is a left-edge call, it's not going to be found through
			// recursion...
			return false;
		}

		try {
			Rule grammarRule = _g.getRule(rule);
			RuleAST ruleAST = grammarRule.ast;

			Deque<Tuple2<GrammarAST, Integer>> worklist = new ArrayDeque<Tuple2<GrammarAST, Integer>>();
			worklist.add(Tuple.create((GrammarAST)ruleAST.getFirstChildWithType(ANTLRParser.BLOCK), -1));
			while (!worklist.isEmpty()) {
				Tuple2<GrammarAST, Integer> current = worklist.poll();
				GrammarAST ast = (GrammarAST)(current.getItem2() >= 0 ? current.getItem1().getChild(current.getItem2()) : current.getItem1());
				switch (ast.getType()) {
				case ANTLRParser.BLOCK:
					for (GrammarAST alt : ast.getAllChildrenWithType(ANTLRParser.ALT)) {
						worklist.add(Tuple.create(alt, -1));
					}
					continue;

				case ANTLRParser.ALT:
					if (ast.getChild(0).getType() != ANTLRParser.EPSILON) {
						worklist.add(Tuple.create(ast, 0));
					}

					continue;

				case ANTLRParser.CLOSURE:
				case ANTLRParser.OPTIONAL:
					assert current.getItem2() >= 0;
					worklist.add(Tuple.create((GrammarAST)ast.getFirstChildWithType(ANTLRParser.BLOCK), -1));
					if (current.getItem2() + 1 < current.getItem1().getChildCount()) {
						worklist.add(Tuple.create(current.getItem1(), current.getItem2() + 1));
					}

					continue;

				case ANTLRParser.ACTION:
				case ANTLRParser.SEMPRED:
					assert current.getItem2() >= 0;
					if (current.getItem2() + 1 < current.getItem1().getChildCount()) {
						worklist.add(Tuple.create(current.getItem1(), current.getItem2() + 1));
					}

					continue;

				case ANTLRParser.RULE_REF:
					if (target.equals(ast.toString())) {
						_knownCalls.put(Tuple.create(rule, target), true);
						return true;
					}

					if (containsLeftEdgeCall(ast.toString(), target, visited)) {
						return true;
					}

					continue;

				case ANTLRParser.STRING_LITERAL:
				case ANTLRParser.WILDCARD:
				case ANTLRParser.NOT:
				case ANTLRParser.SET:
				case ANTLRParser.TOKEN_REF:
					continue;

				default:
					throw new UnsupportedOperationException(String.format("Unknown AST node type %d", ast.getType()));
				}
			}

			_knownCalls.put(Tuple.create(rule, target), false);
			return false;
		}
		finally {
			visited.remove(rule);
		}
	}

	protected RuleVariants createLeftFactoredRuleVariant(Rule rule, String factoredElement) {
		RuleVariants cachedResult = _variants.get(Tuple.create(rule.name, factoredElement));
		if (cachedResult != null) {
			return cachedResult;
		}

		_variants.put(Tuple.create(rule.name, factoredElement), RuleVariants.PROCESSING);

		RuleAST ast = (RuleAST)rule.ast.dupTree();
		BlockAST block = (BlockAST)ast.getFirstChildWithType(ANTLRParser.BLOCK);

		RuleAST unfactoredAst = null;
		BlockAST unfactoredBlock = null;

		if (translateLeftFactoredDecision(block, factoredElement, true, DecisionFactorMode.FULL_FACTOR, false)) {
			// all alternatives factored
		} else {
			ast = (RuleAST)rule.ast.dupTree();
			block = (BlockAST)ast.getFirstChildWithType(ANTLRParser.BLOCK);
			if (!translateLeftFactoredDecision(block, factoredElement, true, DecisionFactorMode.PARTIAL_FACTORED, false)) {
				// no left factored alts
				_variants.put(Tuple.create(rule.name, factoredElement), RuleVariants.NONE);
				return RuleVariants.NONE;
			}

			unfactoredAst = (RuleAST)rule.ast.dupTree();
			unfactoredBlock = (BlockAST)unfactoredAst.getFirstChildWithType(ANTLRParser.BLOCK);
			if (!translateLeftFactoredDecision(unfactoredBlock, factoredElement, true, DecisionFactorMode.PARTIAL_UNFACTORED, false)) {
				throw new IllegalStateException("expected unfactored alts for partial factorization");
			}
		}

		/*
		 * factored elements
		 */
		{
			String variantName = ast.getChild(0).getText() + ATNSimulator.RULE_LF_VARIANT_MARKER + factoredElement;
			((GrammarAST)ast.getChild(0)).token = adaptor.createToken(ast.getChild(0).getType(), variantName);
			GrammarAST ruleParent = (GrammarAST)rule.ast.getParent();
			ruleParent.insertChild(rule.ast.getChildIndex() + 1, ast);
			ruleParent.freshenParentAndChildIndexes(rule.ast.getChildIndex());

			List<GrammarAST> alts = block.getAllChildrenWithType(ANTLRParser.ALT);
			Rule variant = new Rule(_g, ast.getChild(0).getText(), ast, alts.size());
			variant.variant = ATNSimulator.RULE_LF_VARIANT_MARKER;
			variant.setBaseContext(rule.getBaseContext());
			variant.leftFactoredCount = rule.leftFactoredCount + 1;
			if (!_g.defineRule(variant)) {
				throw new IllegalStateException(String.format("Failed to define left-factored rule variant %s", variant.name));
			}

			LOGGER.log(Level.FINE, "Defined left-factored rule variant {0}", variant.name);
			for (int i = 0; i < alts.size(); i++) {
				variant.alt[i + 1].ast = (AltAST)alts.get(i);
			}
		}

		/*
		 * unfactored elements
		 */
		if (unfactoredAst != null) {
			String variantName = unfactoredAst.getChild(0).getText() + ATNSimulator.RULE_NOLF_VARIANT_MARKER + factoredElement;
			((GrammarAST)unfactoredAst.getChild(0)).token = adaptor.createToken(unfactoredAst.getChild(0).getType(), variantName);
			GrammarAST ruleParent = (GrammarAST)rule.ast.getParent();
			ruleParent.insertChild(rule.ast.getChildIndex() + 1, unfactoredAst);
			ruleParent.freshenParentAndChildIndexes(rule.ast.getChildIndex());

			List<GrammarAST> alts = unfactoredBlock.getAllChildrenWithType(ANTLRParser.ALT);
			Rule variant = new Rule(_g, unfactoredAst.getChild(0).getText(), unfactoredAst, alts.size());
			variant.variant = ATNSimulator.RULE_LF_VARIANT_MARKER.equals(rule.variant) ? ATNSimulator.RULE_LF_VARIANT_MARKER : ATNSimulator.RULE_NOLF_VARIANT_MARKER;
			variant.setBaseContext(rule.getBaseContext());
			variant.leftFactoredCount = rule.leftFactoredCount;
			if (!_g.defineRule(variant)) {
				throw new IllegalStateException(String.format("Failed to define non-left-factored rule variant %s", variant.name));
			}

			LOGGER.log(Level.FINE, "Defined non-left-factored rule variant {0}", variant.name);
			for (int i = 0; i < alts.size(); i++) {
				variant.alt[i + 1].ast = (AltAST)alts.get(i);
			}
		}

		/*
		 * result
		 */
		cachedResult = unfactoredAst == null ? RuleVariants.FULLY_FACTORED : RuleVariants.PARTIALLY_FACTORED;
		_variants.put(Tuple.create(rule.name, factoredElement), cachedResult);
		return cachedResult;
	}

	protected enum DecisionFactorMode {

		/**
		 * Alternatives are factored where possible; results are combined, and
		 * both factored and unfactored alternatives are included in the result.
		 */
		COMBINED_FACTOR(true, true),
		/**
		 * Factors all alternatives of the decision. The factoring fails if the
		 * decision contains one or more alternatives which cannot be factored.
		 */
		FULL_FACTOR(true, false),
		/**
		 * Attempts to factor all alternatives of the decision. Alternatives
		 * which could not be factored are not included in the result.
		 */
		PARTIAL_FACTORED(true, false),
		/**
		 * Attempts to factor all alternatives of the decision, and returns the
		 * remaining unfactored alternatives. Alternatives which could be
		 * factored are not included in the result.
		 */
		PARTIAL_UNFACTORED(false, true),
		;

		private final boolean includeFactoredAlts;
		private final boolean includeUnfactoredAlts;

		private DecisionFactorMode(boolean includeFactoredAlts, boolean includeUnfactoredAlts) {
			this.includeFactoredAlts = includeFactoredAlts;
			this.includeUnfactoredAlts = includeUnfactoredAlts;
		}

		public boolean includeFactoredAlts() {
			return includeFactoredAlts;
		}

		public boolean includeUnfactoredAlts() {
			return includeUnfactoredAlts;
		}
	}

	protected enum RuleVariants {
		NONE,
		PARTIALLY_FACTORED,
		FULLY_FACTORED,
		PROCESSING,
	}
}
