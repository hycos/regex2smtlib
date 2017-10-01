import com.github.hycos.regex2smtlib.Translator;
import com.github.hycos.regex2smtlib.translator.exception.FormatNotAvailableException;
import com.github.hycos.regex2smtlib.translator.exception.TranslationException;
import org.junit.Assert;
import org.junit.ClassRule;
import org.junit.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.testcontainers.containers.Container;
import org.testcontainers.containers.GenericContainer;

import java.io.IOException;
import java.util.HashSet;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class TestTranslator {


    final static Logger LOGGER = LoggerFactory.getLogger(TestTranslator.class);

    @ClassRule
    public static GenericContainer z3 =
            new GenericContainer("julianthome/tinned:tinned-z3");

    @ClassRule
    public static GenericContainer cvc4 =
            new GenericContainer("julianthome/tinned:tinned-cvc4");

    // result pattern
    private static Pattern pat = Pattern.compile(".*\"(.*)\".*");


    private static Set<String> patterns = new HashSet<>();

    static {
        patterns.add("((.*)(.)).*(dog).*");
        patterns.add(".*(dog){2,}.*");
        patterns.add("((.*)(.)).*(dog).*");
        patterns.add("((dog)|(truck)){5,}");
        patterns.add("(.*)([A-Za-z].*[0-9].*)");
        patterns.add("(([A-Za-z]){4,}).*(dog).*");
        patterns.add("((([AEIOUaeiou])+)|(dog))(.*)");
        patterns.add(".*(.*)([a-z]).*");
        patterns.add(".*([0-9])|([a-z])|(dog).*");
        patterns.add("(([A-Za-z]){3,}).*([0-9]).*");
        patterns.add("(([A-Za-z]){4,}).*(dog).*");
        patterns.add("(dog.*truck.*)|((.*)(ring))");
        patterns.add("dog{1,2}&&dog");

    }

    public String translateToCVC4(String rexp) {
        String result = "";
        try {
            result = Translator.INSTANCE.translateToConstraint("cvc4", rexp,
                    "v1");

            LOGGER.debug("String {}", result);
        } catch (FormatNotAvailableException | TranslationException e) {
            LOGGER.error("Error {}", e.getMessage());
        }
        return result;
    }


    public String translateToZ3str2(String rexp) {
        String result = "";
        try {
            result = Translator.INSTANCE.translateToConstraint("z3str2",
                    rexp, "v1");

            LOGGER.debug("String {}", result);
        } catch (FormatNotAvailableException | TranslationException e) {
            LOGGER.error("Error {}", e.getMessage());
            Assert.assertTrue(false);
        }
        return result;
    }

    public String translateToZ3(String rexp) {
        String result = "";
        try {
            result = Translator.INSTANCE.translateToConstraint("z3", rexp,
                    "v1");
        } catch (FormatNotAvailableException | TranslationException e) {
            LOGGER.error("Error {}", e.getMessage());
        }
        return result;
    }


    public String solveWithZ3(String rexp) {
        Container.ExecResult result = null;
        String constraint = translateToZ3(rexp);
        String file = "/tmp/" + "f" + constraint.hashCode() + ".smt2";
        String cmd = "echo \'" + constraint + "\' > " + file + " && " + "z3 " + file;
        try {
            result = z3.execInContainer("/bin/bash", "-c" ,cmd);
        } catch (IOException | InterruptedException e) {
            LOGGER.error("error {}", e.getMessage());
            Assert.assertTrue(false);
        }
        return result.getStdout();
    }

    public String solveWithCVC4(String rexp) {
        Container.ExecResult result = null;
        String constraint = translateToCVC4(rexp);
        String cmd = "echo \'" + constraint + "' | cvc4 --lang smt2";
        try {
            result = cvc4.execInContainer("/bin/bash", "-c" ,cmd);
        } catch (IOException | InterruptedException e) {
            LOGGER.error("error {}", e.getMessage());
            Assert.assertTrue(false);
        }
        return result.getStdout();
    }


    @Test
    public void testCVC4() {
        for(String p : patterns){
            String result = solveWithCVC4(p);
            Matcher m = pat.matcher(result.replace("\n", ""));
            Assert.assertTrue(m.matches());
            Assert.assertTrue(m.groupCount() >= 1);
            LOGGER.info("pattern: {}, result: {}", p, m.group(1));
        }
    }


    @Test
    public void testZ3() {
        for(String p : patterns) {
            String result = solveWithZ3(p);
            Matcher m = pat.matcher(result.replace("\n", ""));
            Assert.assertTrue(m.matches());
            Assert.assertTrue(m.groupCount() >= 1);
            LOGGER.info("pattern: {}, result: {}", p, m.group(1));
        }
    }
    
}
