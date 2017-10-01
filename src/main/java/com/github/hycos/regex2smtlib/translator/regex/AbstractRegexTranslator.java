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

package com.github.hycos.regex2smtlib.translator.regex;

import org.apache.commons.lang3.StringUtils;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.snt.inmemantlr.tree.ParseTree;
import org.snt.inmemantlr.tree.ParseTreeNode;
import org.snt.inmemantlr.tree.ParseTreeProcessor;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public abstract class AbstractRegexTranslator extends ParseTreeProcessor <String,String> {

    final static Logger LOGGER = LoggerFactory.getLogger(AbstractRegexTranslator.class);

    protected Map<String, String> vmap = new HashMap<>();

    private String regexVar = "";

    public static int vid = 0;

    public AbstractRegexTranslator(ParseTree regex) {
        super(regex);
    }


    public String putVar(String val) {
        String var = "v" + vid;
        this.regexVar = var;
        this.vmap.put(var, val);
        vid++;
        return var;
    }

    public String createBinaryExpression(String exp, List<ParseTreeNode> nodes) {
        String out = "";

        if(nodes.size() > 1) {
            for (int i = 0; i <= nodes.size()-2; i++) {
                out += " (" + exp + " " + smap.get(nodes.get(i));
            }
            out += " " + smap.get(nodes.get(nodes.size()-1));
            out += StringUtils.repeat(")", nodes.size() - 1);
        } else if (nodes.size() == 1){
            out = smap.get(nodes.get(0));
        }
        return out;
    }

    public void simpleProp(ParseTreeNode n) {

        String s = "";
        if (n.getChildren().size() == 0) {
            smap.put(n, "\"" + n.getEscapedLabel() + "\"");
        } else {
            assert (n.getChildren().size() == 1);
            smap.replace(n, smap.get(n.getChildren().get(0)));
        }
    }

    public String getRegexVar() {
        return this.regexVar;
    }

    public String getRootEntry() {
        return this.smap.get(this.parseTree.getRoot());
    }

    @Override
    protected void initialize() {
        for(ParseTreeNode n : this.parseTree.getNodes()){
            this.smap.put(n, "");
        }
    }


    public abstract String getResult();
    public abstract String getVariables();

    public String getInputString() {
        return getVariables() + "\n\n" + getResult();
    }


}
