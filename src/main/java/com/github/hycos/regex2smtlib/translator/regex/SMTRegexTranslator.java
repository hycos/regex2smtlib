package com.github.hycos.regex2smtlib.translator.regex;

import com.github.hycos.regex2smtlib.translator.TranslationMap;
import com.github.hycos.regex2smtlib.regexparser.RegexParser;
import org.apache.commons.lang3.StringUtils;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.snt.inmemantlr.exceptions.IllegalWorkflowException;
import org.snt.inmemantlr.exceptions.ParsingException;
import org.snt.inmemantlr.tree.ParseTreeNode;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static com.github.hycos.regex2smtlib.translator.TranslationMap.Element.*;


public class SMTRegexTranslator extends RegexTranslator {

    final static Logger LOGGER = LoggerFactory.getLogger(SMTRegexTranslator.class);


    private TranslationMap tmap;
    private EscapingFuntion escaper;


    public SMTRegexTranslator(String regex, TranslationMap tmap,
                              EscapingFuntion esc)
            throws
            IllegalWorkflowException, ParsingException {
        // obtain the parse tree from the regular expression an process it
        super(RegexParser.INSTANCE.parse(regex));

        // visualize parse tree in dot format
        LOGGER.debug("{}", this.parseTree.toDot());
        this.tmap = tmap;
        this.escaper = esc;
    }

    public SMTRegexTranslator(String regex, TranslationMap tmap)
            throws
            IllegalWorkflowException, ParsingException {
        this(regex, tmap, new SmtEscape());
    }


    public String getAny() {
        if(tmap.has(RANGE)) {
            return tmap.get(RANGE);
        } else {
            char from = '!';
            char to = '}';
            String any = "(" + tmap.get(RANGE) + "\"" + from + "\" \"" + to + "\")";
            return any;
        }
    }

    @Override
    protected void process(ParseTreeNode n) {

        LOGGER.info("Handle " + n.getId() + " " + n.getRule());

        switch (n.getRule()) {

            case "root":
            case "capture":
                simpleProp(n);
                break;
            case "alternation":
                if (n.getChildren().size() == 1) {
                    simpleProp(n);
                    break;
                }
                String alt = createBinaryExpression(tmap.get(UNION), n.getChildren());
                //alt = "(assert (" + MEMBERSHIP + " v" + vid + " " + alt + " ))";
                //String salt = putVar(alt);
                smap.put(n, alt);
                break;
            case "expr":
                if (n.getChildren().size() == 1) {
                    simpleProp(n);
                    break;
                }
                boolean concat = true;
                for (ParseTreeNode c : n.getChildren()) {
                    if (!c.getRule().equals("element")) {
                        concat = false;
                    }
                }
                if (concat) {
                    String sconcat = createBinaryExpression(tmap.get(CONCAT), n
                            .getChildren());
                    //sconcat = "(assert (" + MEMBERSHIP + " v" + vid + " " + sconcat + "))";
                    //String sexpr = putVar(sconcat);
                    smap.put(n, sconcat);
                }
                break;
            case "element":

                if (n.getChildren().size() == 1) {
                    simpleProp(n);
                } else if (n.getChildren().size() == 2) {

                    ParseTreeNode last = n.getChildren().get(1);
                    ParseTreeNode first = n.getChildren().get(0);

                    LOGGER.info("FIRST " + first.getEscapedLabel() + ">> " + first.getId() + " " + smap.get(first));
                    LOGGER.info("LParseTree " + last.getEscapedLabel() + ">> " + last.getId() + " " + smap.get(last));


                    String lbl = last.getLabel();

                    if (last != null && last.getRule().equals("quantifier")) {
                        switch (lbl) {
                            case "*":
                                String star = "(" + tmap.get(STAR) + " " + smap
                                        .get(first) + " )";
                                //String starvar = putVar(star);
                                //smap.put(n, starvar);
                                smap.put(n,star);
                                break;
                            case "+":
                                String plus = "(" + tmap.get(PLUS) + " " + smap
                                        .get(first) + " )";
                                smap.put(n,plus);
                                break;
                            case "?":

                                if(tmap.has(OPT)) {
                                    String opt = "(" + tmap.get(OPT) + " " + smap
                                            .get(first) + " )";
                                    smap.put(n, opt);
                                } else {
                                    lbl = "{0,1}";
                                }
                                break;
                        }

                        int min = -1;
                        int max = -1;
                        Pattern pattern = Pattern.compile("\\{([0-9]*),?([0-9]*)\\}");
                        Matcher matcher = pattern.matcher(lbl);


                        if (matcher.matches()) {
                            if (matcher.group(1) != null) {
                                min = Integer.parseInt(matcher.group(1));
                            }
                            if (matcher.group(2) != null) {
                                max = Integer.parseInt(matcher.group(2));
                            }


                            String smin = "";
                            String sran = "";

                            if (min > 0) {
                                for (int i = 1; i < min; i++) {
                                    smin += " (" + CONCAT + " " + smap.get(first);
                                }
                                smin += " " + smap.get(first);
                                smin += StringUtils.repeat(")", min - 1);
                            } else if (min <= 0) {
                                smin += "\"\"";
                            }


                            if (max > -1) {

                                String unroll = smin;
                                for (int i = min; i < max; i++) {
                                    sran += " (" + UNION + " " + unroll;
                                    unroll = " (" + CONCAT + " " + this.smap.get(first) + "  " + unroll + ")";
                                }
                                sran += " " + unroll;
                                sran += StringUtils.repeat(")", max - min);
                            } else if (max <= 0) {
                                sran = " (" + CONCAT + " " + smin + " (Star " + smin + "))";
                            }


                            //String result = "(assert (" + MEMBERSHIP + " v" + vid + sran + "))";
                            //String var = putVar(result);

                            //smap.put(n, var);

                            smap.put(n, sran);
                            LOGGER.info("min " + min + " max" + max);
                        }
                    }
                }

                break;

            case "number":
            case "letter":
            case "literal":
            case "cc_literal":
            case "shared_literal":
                String label = " (" + CONV + " " + "\"" + esc(n.getLabel()) + "\")";
                this.smap.put(n,label);
                break;
            case "atom":
                if(n.isLeaf()) {
                    if(n.getLabel().equals(".")) {
                        smap.put(n, getAny());
                    }
                } else {
                    simpleProp(n);
                }
                break;
            case "cc_atom":
                if (n.getChildren().size() == 0) {
                    ;
                } else if (n.getChildren().size() == 1) {
                    simpleProp(n);
                } else {
                    assert(n.getChildren().size() == 2);
                    ParseTreeNode first = n.getChildren().get(0);
                    ParseTreeNode lParseTree = n.getChildren().get(1);
                    String rex = "(" + RANGE + " \"" + esc(first.getLabel()) + "\" \"" + esc(lParseTree.getLabel()) + "\")";
                    smap.put(n, rex);
                }
                break;
            case "character_class":
                if (n.getChildren().size() == 1) {
                    simpleProp(n);
                } else {
                    String cc = "";
                    int i = 0;
                    for(i = 0; i < n.getChildren().size() - 1; i++) {
                        ParseTreeNode c = n.getChildren().get(i);
                        cc += " (" + UNION + " " + this.smap.get(c);
                    }
                    cc += " " + this.smap.get(n.getChildren().get(i));
                    cc += StringUtils.repeat(")", n.getChildren().size()-1);
                    smap.put(n, cc);
                }
                break;
        }

    }

    private String esc(String s) {
        return escaper.escape(s);
    }

    @Override
    public String getResult() {
        LOGGER.info(debug());
        return getRootEntry();
    }

    @Override
    public String getVariables() {
        return "";
    }


}
