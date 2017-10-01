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

import com.github.hycos.regex2smtlib.translator.exception.TranslationException;

public interface TranslatorIface {
    /**
     * translates regular expression string to SMT-LIB format
     * @param regex regular expression string
     * @return regular expression in SMT-LIB format
     * @throws TranslationException somehting went wrong during the translation
     */
    String translate(String regex) throws TranslationException;

    /**
     * return a translation map, i.e., a mapping table that maps
     * regular expression operations to native operations
     * @return translation map
     */
    TranslationMap getTmap();

    /**
     * get the name of the translator
     * @return String that uniquely identifies the translator
     */
    String getName();
}
