package com.github.hycos.regex2smtlib.translator.regex;

import java.util.Objects;

public class SmtEscape implements EscapingFuntion {

    @Override
    public String escape(String input) {

        Objects.requireNonNull(input, "input should not be null");

        StringBuilder out = new StringBuilder();

        char carr[] = input.toCharArray();
        for(int k = 0; k < carr.length; k ++) {
            char c = carr[k];
            if(c == '\"') {
                out.append("\"");
            }
            out.append(c);
        }
        return out.toString();


    }
}
