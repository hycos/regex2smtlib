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

package com.github.hycos.regex2smtlib.translator;

import static com.github.hycos.regex2smtlib.translator.TranslationMap.Element.*;

public class Z3Translator extends AbstractTranslator {

    private static TranslationMap tmap = new TranslationMap();

    static {
        tmap.put(CONCAT, "re.++");
        tmap.put(PLUS, "re.+");
        tmap.put(UNION, "re.union");
        tmap.put(INTERSECTION, "re.inter");
        tmap.put(STAR, "re.*");
        tmap.put(MEMBERSHIP, "str.in.re");
        tmap.put(CONV, "str.to.re");
        tmap.put(RANGE, "re.range");
        tmap.put(OPT, "re.opt");
        tmap.put(ALLCHAR, "re.allchar");
    }

    public TranslationMap getTmap() {
        return tmap;
    }

    public String getName(){
        return "z3";
    }


}
