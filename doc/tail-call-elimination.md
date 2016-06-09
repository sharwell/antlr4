# Tail Call Elimination

This article describes the application of tail call elimination to the ATN configurations used within the ALL(\*)
implementation. Since tail call elimination is not required for a correct implementation of the ALL(\*) closure
algorithm and does not affect the ALL(\*) algorithmic complexity, it is considered an implementation optimization within
ANTLR 4 itself.

## Background

ANTLR's ALL(\*) algorithm relies heavily on a closure operation performed on ATN configurations. A key component of
these configurations is a directed graph representing the return sites for rule invocations which occurred. This graph
is very similar to the call stack one would observe in debugging a language like Java, except that it holds information
about the *return* site instead of the *call* site.

> :memo: The distinction between return sites and call sites does not affect the applicability of tail call elimination,
> but it does affect the implementation of it. ANTLR represents the rule invocation graph in this form due to its
> improved ability to reduce the size of the graphs that occur in practice.

In a basic ALL(\*) implementation, the context graph associated with ATN configurations could represent the complete set
of return sites for rule invocations encountered. However, in some cases this comprehensive graph contains return sites
which can never influence the outcome of the prediction algorithm. By identifying return sites that could never
influence the outcome and removing them from the context graph, several benefits are realized:

1. The memory required to store a single DFA state is reduced since fewer prediction context instances appear in the ATN
   configurations that are part of the state.
2. The critical closure operation performed on ATN configurations takes less time by no longer following certain
   transitions in the ATN which are known to not affect the outcome of prediction.
3. When two DFA states each contain information that is known to not affect the outcome of prediction, the elimination
   of this information from each of the two states may result in the two states becoming equivalent. This can occur when
   the only difference(s) between the two DFA states lies within the information that is known to not affect the outcome
   of prediction. Numerous benefits related to cache hits and memory reduction are realized when equivalent DFA states
   are identified and combined.

## Unnecessary Return States

The specific "information known to not affect the outcome of prediction" identified and removed by the tail call
elimination process in ANTLR 4 is rule return states that appear in the prediction context associated with an ATN
configuration. In most cases, tail calls (which are rule references which appear on the right edge of a rule) meet this
condition. The simplest form of this could look like the following:

```antlr
foo : A;
bar : B foo;
```

In the example, the invocation of **foo** within **bar** is a tail call. During a closure operation after matching a
token **B**, the return state from **foo** does not need to be pushed onto the prediction context for the ATN
configuration. If we reach the end of **foo** later in the prediction process, we can return directly to the callers of
**B** without first returning to **B** itself.

*TODO: More information necessary?*

The general approach for identifying rule invocations with unnecessary return states is to perform a LL(1) lookahead
from the return state of the rule invocation, where `EPSILON` is added to the lookahead set if the end of the rule is
reached. If the resulting set *only* contains `EPSILON`, then the call is a tail call for the purpose of this
optimization.

## Special Considerations

### Lexer

The ANTLR lexer assigns token types by examining the rule stop state(s) reached during prediction. For example, consider
the following grammar:

```antlr
A : 'a';
BA : 'b' A;
```

When matching the input `ba`, it's important for the prediction algorithm in the lexer to recognize that at the end of
matching `ba`, the prediction stops at the end of rule **BA**. Even though no more symbols are consumed after matching
`a` within rule **A**, if prediction were to stop immediately it would assign token type **A** to the input `ba`. While
this limits the application of tail call elimination in some scenarios, it remains applicable in other scenarios. For
example, consider the following grammar which matches the same inputs as the previous one:

```antlr
A : 'a';
I : A;
BA : 'b' Intermediate;
```

In this case, when matching `ba` the important consideration is the return path to the rule stop state for **BA**. When
the closure after matching `b` reaches the rule invocation for **A** inside **I**, the tail call elimination would apply
without any loss of information. The resulting prediction context graph would indicate that after matching `a`, the
closure should immediately return to the state in **BA** after the invocation of **I**, without first stopping at an
intermediate state in **I**. In other words, the ATN configuration will look as though **B** directly invoked **A**.

### SLL Prediction

*TODO*

## Algorithmic Complexity

*TODO*
