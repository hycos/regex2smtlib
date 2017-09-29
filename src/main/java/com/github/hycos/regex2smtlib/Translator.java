package com.github.hycos.regex2smtlib;

import com.github.hycos.regex2smtlib.translator.CVC4Translator;
import com.github.hycos.regex2smtlib.translator.TranslatorInterface;
import com.github.hycos.regex2smtlib.translator.Z3Str2Translator;
import com.github.hycos.regex2smtlib.translator.Z3Translator;
import com.github.hycos.regex2smtlib.translator.exception.FormatNotAvailableException;
import com.github.hycos.regex2smtlib.translator.exception.TranslationException;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

public enum Translator {

    INSTANCE;

    private static Map<String, TranslatorInterface> translators = new
            HashMap<>();


    static {
        translators.put(Z3Translator.INSTANCE.getName(), Z3Translator.INSTANCE);
        translators.put(CVC4Translator.INSTANCE.getName(), CVC4Translator.INSTANCE);
        translators.put(Z3Str2Translator.INSTANCE.getName(), Z3Str2Translator.INSTANCE);
    }


    public Set<String> getAvailableFormats() {
        return new TreeSet(translators.keySet());
    }

    public String translate(String format, String regex) throws
            FormatNotAvailableException, TranslationException {

        if(!translators.containsKey(format)) {
            throw new FormatNotAvailableException("Format is not available " +
                    "and should be one of: " + getAvailableFormats().toString
                    ());
        }

        return translators.get(format).translate(regex);
    }


    public String translate(String format, String regex, String vname) throws
            FormatNotAvailableException, TranslationException {

        return "";
    }

    public String translateAndGenerateConstraint(String format, String regex,
                                             String vname) throws
            FormatNotAvailableException, TranslationException {

        return "";
    }






}
