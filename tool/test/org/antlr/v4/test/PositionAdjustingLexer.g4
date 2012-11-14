lexer grammar PositionAdjustingLexer;

@members {
	public boolean testAssertion(int assertionMode, int passingRule) {
		int index = _input.index();
		int mark = _input.mark();
		try {
			LexerATNSimulator interp = new LexerATNSimulator(this, _ATN, _decisionToDFA, _sharedContextCache);
			interp.copyState(_interp);
			int result = interp.match(_input, assertionMode);
			return result == passingRule;
		} finally {
			_input.seek(index);
			_input.release(mark);
		}
	}
}

ASSIGN : '=' ;
PLUS_ASSIGN : '+=' ;
LCURLY:	'{';

// 'tokens' followed by '{'
TOKENS : 'tokens' {testAssertion(MODE_TOKENS_ASSERTION_1, TOKENS_ASSERTION_1_PASS)}?;

// IDENTIFIER followed by '+=' or '='
LABEL
	:	IDENTIFIER {testAssertion(MODE_LABEL_ASSERTION_1, LABEL_ASSERTION_1_PASS)}?
	;

IDENTIFIER
	:	[a-zA-Z_] [a-zA-Z0-9_]*
	;

fragment
IGNORED
	:	[ \t\r\n]*
	;

NEWLINE
	:	[\r\n]+ -> skip
	;

WS
	:	[ \t]+ -> skip
	;

mode MODE_TOKENS_ASSERTION_1;

	TOKENS_ASSERTION_1_PASS : IGNORED '{';
	TOKENS_ASSERTION_1_FAIL : .;

mode MODE_LABEL_ASSERTION_1;

	LABEL_ASSERTION_1_PASS : IGNORED '+'? '=';
	LABEL_ASSERTION_1_FAIL : .;
