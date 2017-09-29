package com.github.hycos.regex2smtlib.translator;


import java.util.HashMap;
import java.util.Map;

public class TranslationMap {

    public enum Element {
        CONCAT,
        PLUS,
        UNION,
        STAR,
        MEMBERSHIP,
        EQUALITY,
        CONV,
        EQ,
        RANGE,
        OPT,
        ALLCHAR
    }

    private Map<Element, String> tmap = new HashMap();

    public TranslationMap(){
        for (Element element : Element.values()) {
            tmap.put(element, "");
        }
    }

    public void put(Element ele, String trans) {
        tmap.put(ele,trans);
    }

    public String get(Element ele) {
        return tmap.get(ele);
    }

    public boolean has(Element ele) {
        return tmap.containsKey(ele);
    }


}
