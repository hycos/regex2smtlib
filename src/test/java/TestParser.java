import com.github.hycos.regex2smtlib.regexparser.RegexParser;
import org.junit.Test;
import org.snt.inmemantlr.exceptions.IllegalWorkflowException;
import org.snt.inmemantlr.exceptions.ParsingException;

public class TestParser {

    @Test
    public void testParser() {
        try {
            RegexParser.INSTANCE.parse("abc*");
        } catch (IllegalWorkflowException e) {
            e.printStackTrace();
        } catch (ParsingException e) {
            e.printStackTrace();
        }
    }
}
