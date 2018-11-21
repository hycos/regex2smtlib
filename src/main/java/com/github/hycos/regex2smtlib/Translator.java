/**
 * regex2smtlib: A regex to smtlib translator
 *
 * The MIT License (MIT)
 *
 * Copyright (c) 2017 Julian Thome <julian.thome.de@gmail.com>
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 **/

package com.github.hycos.regex2smtlib;

import com.github.hycos.regex2smtlib.translator.*;
import com.github.hycos.regex2smtlib.translator.exception.FormatNotAvailableException;
import com.github.hycos.regex2smtlib.translator.exception.TranslationException;
import com.ibm.icu.impl.Assert;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.trimou.Mustache;
import org.trimou.engine.MustacheEngine;
import org.trimou.engine.MustacheEngineBuilder;
import org.trimou.engine.locator.ClassPathTemplateLocator;
import org.trimou.engine.locator.TemplateLocator;

import java.io.Reader;
import java.io.StringReader;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

public enum Translator {

    INSTANCE;

    final static Logger LOGGER = LoggerFactory.getLogger(Translator.class);

    private static Map<String,String> templates = new HashMap<>();
    private static Map<String, AbstractTranslator> translators = new HashMap<>();
    private static MustacheEngine mustache = null;

    static {
        templates.put("conjunct", "(assert ({{membership}} {{vname}} {{& smtregex}}))");
        templates.put("template", "{{#cvc4}}\n" +
                "(set-logic QF_S)\n" +
                "(set-option :produce-models true)\n" +
                "(set-option :strings-exp true)\n" +
                "(declare-fun {{vname}} () String)\n" +
                "{{/cvc4}}\n" +
                "{{#z3}}(declare-fun {{vname}} () String){{/z3}}\n" +
                "{{#z3str2}}(declare-const {{vname}} String){{/z3str2}}\n" +
                "{{<conjunct}}{{/conjunct}}\n" +
                "(check-sat)\n" +
                "(get-model)");
        addTranslators(new CVC4Translator(), new Z3Str2Translator(), new Z3Translator());

        TemplateLocator myLocator = new TemplateLocator() {
            @Override
            public Reader locate(String s) {
                return new StringReader(templates.get(s));
            }
        };

        mustache = MustacheEngineBuilder
                .newBuilder()
                .addTemplateLocator(myLocator).build();

    }

    private static void addTranslators(AbstractTranslator... trans) {
        for (AbstractTranslator tran : trans) {
            translators.put(tran.getName(), tran);
        }
    }

    /**
     * show all availabe formats to which a regular expression can be converted
     * @return set of available formats
     */
    public Set<String> getAvailableFormats() {
        return new TreeSet(translators.keySet());
    }

    /**
     * translate a regular expression to a specific format
     * @param format format to which the regular expression should be converted
     * @param regex regular expression string in PCRE format
     * @return smt constraint representing regex
     * @throws FormatNotAvailableException specified format not available
     * @throws TranslationException somehting went wrong during the translation
     */
    public String translate(String format, String regex) throws
            FormatNotAvailableException, TranslationException {

        if(!translators.containsKey(format)) {
            throw new FormatNotAvailableException("Format is not available " +
                    "and should be one of: " + getAvailableFormats().toString
                    ());
        }

        return translators.get(format).translate(regex);
    }


    /**
     * translate a regular expression to a specific format and generate
     * a conjunct
     * @param format format to which the regular expression should be converted
     * @param regex regular expression string in PCRE format
     * @param vname variable name which should be matched against regex
     * @return smt conjunct matching vname against regex
     * @throws FormatNotAvailableException specified format not available
     * @throws TranslationException somehting went wrong during the translation
     */
    public String translateToClause(String format, String regex, String
            vname) throws
            FormatNotAvailableException, TranslationException {
        return render("conjunct", format, translate(format,regex), vname);
    }

    /**
     * translate a regular expression to a specific format and generate
     * a constraint
     * @param format format to which the regular expression should be converted
     * @param regex regular expression string in PCRE format
     * @param vname variable name which should be matched against regex
     * @return smt constraint matching vname against regex
     * @throws FormatNotAvailableException specified format not available
     * @throws TranslationException somehting went wrong during the translation
     */
    public String translateToConstraint(String format, String regex, String
            vname) throws
            FormatNotAvailableException, TranslationException {
        return render("template", format, translate(format,regex), vname);
    }

    private String render(String template,
                          String format,
                          String smtregex,
                          String vname) {

        assert(templates.containsKey(template));

        HashMap<String,String> data = new HashMap<>();

        data.put(format, format);
        data.put("vname", vname);
        data.put("membership", translators.get(format).getTmap().get
                (TranslationMap.Element.MEMBERSHIP));
        data.put("smtregex", smtregex);
        String out = mustache.getMustache(template).render(data);
        return out;
    }

}
