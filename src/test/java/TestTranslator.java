import com.github.hycos.regex2smtlib.Translator;
import com.github.hycos.regex2smtlib.translator.exception.FormatNotAvailableException;
import com.github.hycos.regex2smtlib.translator.exception.TranslationException;
import org.junit.Assert;
import org.junit.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class TestTranslator {

    final static Logger LOGGER = LoggerFactory.getLogger(TestTranslator.class);

    @Test
    public void testCVC4() {


        try {
            String result = Translator.INSTANCE.translate("cvc4", "abc*" +
                    "(de[f-z])+");

            LOGGER.debug("String {}", result);
        } catch (FormatNotAvailableException | TranslationException e) {
            Assert.assertTrue(false);
        }
    }


    @Test
    public void testZ3str2() {

    }

    @Test
    public void testZ3() {

    }



}
