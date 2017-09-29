package com.github.hycos.regex2smtlib.translator;

import com.github.hycos.regex2smtlib.translator.exception.TranslationException;

public interface TranslatorInterface {
    String translate (String rexp) throws TranslationException;
    String getName();
}
