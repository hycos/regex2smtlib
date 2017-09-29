package com.github.hycos.regex2smtlib.regexparser;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.snt.inmemantlr.GenericParser;
import org.snt.inmemantlr.exceptions.CompilationException;
import org.snt.inmemantlr.exceptions.IllegalWorkflowException;
import org.snt.inmemantlr.exceptions.ParsingException;
import org.snt.inmemantlr.listener.DefaultTreeListener;
import org.snt.inmemantlr.tree.ParseTree;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;


public enum RegexParser {

    INSTANCE;

    final static Logger LOGGER = LoggerFactory.getLogger(RegexParser.class);

    private static Set<String> filter = new HashSet<String>(Arrays.asList(
            new String[]{"alternation",
            "expr", "literal",
            "quantifier", "atom", "letter", "number", "element",
            "character_class", "cc_atom", "cc_literal"
    }));

    private static GenericParser gp = null;
    private static DefaultTreeListener dlist = null;
    private static String gfile = RegexParser.class.getClassLoader().getResource
            ("Regex.g4")
            .getFile();


    static {
        LOGGER.debug("gfile {}", gfile);

        File f = new File(gfile);
        try {
            gp = new GenericParser(f);
        } catch (FileNotFoundException e) {
            LOGGER.debug(e.getMessage());
            System.exit(-1);
        }

        dlist = new DefaultTreeListener(s -> filter.contains(s));

        gp.setListener(dlist);
        try {
            gp.compile();
        } catch (CompilationException e) {
            LOGGER.debug(e.getMessage());
            System.exit(-1);
        }
    }


    public ParseTree parse(String regex) throws IllegalWorkflowException, ParsingException {
        gp.parse(regex);
        return dlist.getParseTree();
    }

}
