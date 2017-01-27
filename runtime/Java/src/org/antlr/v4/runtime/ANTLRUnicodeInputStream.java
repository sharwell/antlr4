/*
 * Copyright (c) 2012-2016 The ANTLR Project. All rights reserved.
 * Use of this file is governed by the BSD 3-clause license that
 * can be found in the LICENSE.txt file in the project root.
 */
package org.antlr.v4.runtime;

import org.antlr.v4.runtime.misc.IntegerList;

import java.io.IOException;
import java.io.InputStream;
import java.io.Reader;

/**
 * A {@link CharStream} which provides a sequence of Unicode code points.
 *
 * <p>The underlying data for this stream is a {@link String}, which is UTF-16
 * encoded in Java.</p>
 */
public class ANTLRUnicodeInputStream extends ANTLRInputStream {
	private final IntegerList multibyteIndexes = new IntegerList();
	private final IntegerList multibyteCharacters = new IntegerList();

	private int multibyteListIndex;
	private int range;

	private int la1;

	public ANTLRUnicodeInputStream() {
		super();
		this.la1 = LA1CodeUnit();
	}

	/** Copy data in string to a local char array */
	public ANTLRUnicodeInputStream(String input) {
		super(input);
		this.la1 = LA1CodeUnit();
	}

	/** This is the preferred constructor for strings as no data is copied */
	public ANTLRUnicodeInputStream(char[] data, int numberOfActualCharsInArray) {
		super(data, numberOfActualCharsInArray);
		this.la1 = LA1CodeUnit();
	}

	public ANTLRUnicodeInputStream(Reader r) throws IOException {
		super(r);
		this.la1 = LA1CodeUnit();
	}

	public ANTLRUnicodeInputStream(Reader r, int initialSize) throws IOException {
		super(r, initialSize);
		this.la1 = LA1CodeUnit();
	}

	public ANTLRUnicodeInputStream(Reader r, int initialSize, int readChunkSize) throws IOException {
		super(r, initialSize, readChunkSize);
		this.la1 = LA1CodeUnit();
	}

	public ANTLRUnicodeInputStream(InputStream input) throws IOException {
		super(input);
		this.la1 = LA1CodeUnit();
	}

	public ANTLRUnicodeInputStream(InputStream input, int initialSize) throws IOException {
		super(input, initialSize);
		this.la1 = LA1CodeUnit();
	}

	public ANTLRUnicodeInputStream(InputStream input, int initialSize, int readChunkSize) throws IOException {
		super(input, initialSize, readChunkSize);
		this.la1 = LA1CodeUnit();
	}

	@Override
	public void consume() {
		if (la1 < Character.MIN_HIGH_SURROGATE || la1 > Character.MAX_HIGH_SURROGATE) {
			super.consume();
			la1 = LA1CodeUnit();
			return;
		}

		// maxe sure the next character has been processed
		this.LA(1);

		if (multibyteListIndex >= multibyteIndexes.size() || multibyteIndexes.get(multibyteListIndex) != index()) {
			super.consume();
		}
		else {
			// consume both surrogates
			super.consume();
			super.consume();

			multibyteListIndex++;
		}

		la1 = LA1CodeUnit();
		assert range >= index();
	}

	@Override
	public int LA(int i) {
		if (i == 1 && (la1 < Character.MIN_HIGH_SURROGATE || la1 > Character.MAX_HIGH_SURROGATE)) {
			return this.la1;
		}

		if (i <= 0) {
			int desiredIndex = index() + i;
			for (int j = multibyteListIndex - 1; j >= 0; j--) {
				if (multibyteIndexes.get(j) + 1 > desiredIndex) {
					desiredIndex--;
				}

				if (multibyteIndexes.get(j) == desiredIndex) {
					return multibyteCharacters.get(j);
				}
			}

			return super.LA(desiredIndex - index());
		}
		else {
			int desiredIndex = index() + i - 1;
			for (int j = multibyteListIndex; j < multibyteIndexes.size(); j++) {
				if (multibyteIndexes.get(j) == desiredIndex) {
					return multibyteCharacters.get(j);
				}
				else if (multibyteIndexes.get(j) < desiredIndex) {
					desiredIndex++;
				}
				else {
					return super.LA(desiredIndex - index() + 1);
				}
			}

			int[] currentIndex = { index() };
			for (int j = 0; j < i; j++) {
				int previousIndex = currentIndex[0];
				int c = readCodePointAt(currentIndex);
				if (currentIndex[0] > range) {
					if (currentIndex[0] - previousIndex > 1) {
						multibyteIndexes.add(previousIndex);
						multibyteCharacters.add(c);
					}

					range = currentIndex[0];
				}

				if (j == i - 1) {
					return c;
				}
			}

			throw new IllegalStateException("shouldn't be reachable");
		}
	}

	@Override
	public void seek(int index) {
		super.seek(index);

		la1 = LA1CodeUnit();
		multibyteListIndex = multibyteIndexes.binarySearch(index());
		if (multibyteListIndex < 0) {
			multibyteListIndex = -multibyteListIndex - 1;
		}
	}

	private int readCodePointAt(int[] nextIndexPtr) {
		assert nextIndexPtr != null && nextIndexPtr.length == 1;

		int c0 = super.LA(nextIndexPtr[0] - index() + 1);
		if (c0 >= Character.MIN_HIGH_SURROGATE && c0 <= Character.MAX_HIGH_SURROGATE) {
			int c1 = super.LA(nextIndexPtr[0] - index() + 2);
			if (c1 >= Character.MIN_LOW_SURROGATE && c1 <= Character.MAX_LOW_SURROGATE) {
				int value = Character.toCodePoint((char)c0, (char)c1);
				nextIndexPtr[0] += 2;
				return value;
			}
		}

		nextIndexPtr[0]++;
		return c0;
	}

	private int LA1CodeUnit() {
		if (p >= n) {
			return IntStream.EOF;
		}

		return data[p];
	}
}
