package com.github.hycos.regex2smtlib.translator;

import com.github.hycos.regex2smtlib.translator.regex.SMTRegexTranslator;
import com.github.hycos.regex2smtlib.translator.exception.TranslationException;
import org.snt.inmemantlr.exceptions.IllegalWorkflowException;
import org.snt.inmemantlr.exceptions.ParsingException;

import static com.github.hycos.regex2smtlib.translator.TranslationMap.Element.*;

public enum Z3Translator implements TranslatorInterface {

    INSTANCE;

    private static TranslationMap tmap = new TranslationMap();

    static {
        tmap.put(CONCAT, "re.++");
        tmap.put(PLUS, "re.+");
        tmap.put(UNION, "re.union");
        tmap.put(STAR, "re.*");
        tmap.put(MEMBERSHIP, "str.in.re");
        tmap.put(CONV, "str.to.re");
        tmap.put(EQ, "=");
        tmap.put(RANGE, "re.range");

        tmap.put(OPT, "re.opt");
        tmap.put(ALLCHAR, "re.allchar");
    }

    public String translate(String regex) throws TranslationException {
        try {
            return new SMTRegexTranslator(regex, tmap).getResult();
        } catch (IllegalWorkflowException | ParsingException e) {
            throw new TranslationException(e.getMessage());
        }
    }

    public String getName(){
        return "z3";
    }


}
