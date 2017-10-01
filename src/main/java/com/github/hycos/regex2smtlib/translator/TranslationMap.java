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

import java.util.HashMap;
import java.util.Map;

public class TranslationMap {

    /**
     * enum for various operations related to
     * regular expressions
     */
    public enum Element {
        CONCAT, /* concatnation */
        PLUS, /* Kleene plus */
        STAR, /* Kleene star */
        UNION, /* Regular language union */
        CONV, /* convert string to regex */
        RANGE, /* character range */
        OPT, /* zero or one (?,{0,1}) */
        ALLCHAR, /* regular expression accepting every char (.) */
        INTERSECTION, /* Regular expression intersection */
        MEMBERSHIP /* regular expression membership */
    }

    private Map<Element, String> tmap = new HashMap();

    public TranslationMap(){
        for (Element element : Element.values()) {
            tmap.put(element, "");
        }
    }

    /**
     * Add element to translation map
     * @param ele regular expression element
     * @param trans string that represents ele w.r.t. the translator
     */
    public void put(Element ele, String trans) {
        tmap.put(ele,trans);
    }

    /**
     * get translation of element
     * @param ele regular expression element
     * @return string that represents ele w.r.t. the translator
     */
    public String get(Element ele) {
        return tmap.get(ele);
    }

    /**
     * check the presence of ele in translation map
     * @param ele regular expression element
     * @return true, in case ele is present in translation map
     */
    public boolean has(Element ele) {
        return tmap.containsKey(ele) && !tmap.get(ele).isEmpty();
    }


}
