/**
 * regex2smtlib: A regex to smtlib translator
 * <p>
 * The MIT License (MIT)
 * <p>
 * Copyright (c) 2017 Julian Thome <julian.thome.de@gmail.com>
 * <p>
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 * <p>
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 * <p>
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 **/


package com.github.hycos.regex2smtlib.regexparser;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.snt.inmemantlr.GenericParser;
import org.snt.inmemantlr.exceptions.CompilationException;
import org.snt.inmemantlr.exceptions.IllegalWorkflowException;
import org.snt.inmemantlr.exceptions.ParsingException;
import org.snt.inmemantlr.listener.DefaultTreeListener;
import org.snt.inmemantlr.tree.ParseTree;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Scanner;
import java.util.Set;


public enum RegexParser {

    INSTANCE;

    final static Logger LOGGER = LoggerFactory.getLogger(RegexParser.class);

    private static Set<String> filter = new HashSet<>(Arrays.asList(
            new String[]{"alternation", "intersection",
                    "expr", "literal",
                    "quantifier", "atom", "letter", "number", "element",
                    "character_class", "cc_atom", "cc_literal"
            }));

    private static GenericParser gp = null;
    private static DefaultTreeListener dlist = null;


    static {
        gp = new GenericParser(load());

        dlist = new DefaultTreeListener(s -> filter.contains(s));

        gp.setListener(dlist);
        try {
            gp.compile();
        } catch (CompilationException e) {
            LOGGER.error(e.getMessage());
            System.exit(-1);
        }
    }


    private static String load() {
        return new Scanner(RegexParser
                .class
                .getResourceAsStream(
                        "/com/github/hycos/regex2smtlib/Regex.g4"),
                "UTF-8").useDelimiter("\\A").next();
    }

    /**
     * parse regex string and return corresponding parse tree
     * @param regex regular expression string
     * @return parse tree of regex
     * @throws IllegalWorkflowException there went something wrong during
     * parser generation
     * @throws ParsingException regular expression is not in PRCRE format
     */
    public ParseTree parse(String regex) throws IllegalWorkflowException,
            ParsingException {
        gp.parse(regex);
        return dlist.getParseTree();
    }

}
