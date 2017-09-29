package com.github.hycos.regex2smtlib.translator;

import com.github.hycos.regex2smtlib.translator.regex.SMTRegexTranslator;
import com.github.hycos.regex2smtlib.translator.exception.TranslationException;
import org.snt.inmemantlr.exceptions.IllegalWorkflowException;
import org.snt.inmemantlr.exceptions.ParsingException;

import static com.github.hycos.regex2smtlib.translator.TranslationMap.Element.*;

public enum Z3Str2Translator implements TranslatorInterface {

    INSTANCE;

    private static TranslationMap tmap = new TranslationMap();

    static {
        tmap.put(CONCAT, "RegexConcat");
        tmap.put(PLUS, "RegexPlus");
        tmap.put(UNION, "RegexUnion");
        tmap.put(STAR, "RegexStar");
        tmap.put(MEMBERSHIP, "RegexIn");
        tmap.put(CONV, "Str2Reg");
        tmap.put(EQ, "=");
        tmap.put(RANGE, "RegexCharRange");
        tmap.put(OPT, "");
        tmap.put(ALLCHAR, "");
    }

    public String translate(String regex) throws TranslationException {
        try {
            return new SMTRegexTranslator(regex, tmap).getResult();
        } catch (IllegalWorkflowException | ParsingException e) {
            throw new TranslationException(e.getMessage());
        }
    }

    public String getName(){
        return "z3str2";
    }

}
