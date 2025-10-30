package fr.univreunion.rati.rank;

import static org.junit.Assert.assertTrue;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Pattern;
import java.util.stream.Stream;

import org.junit.Test;

/**
 * Locks in RaTI's independence: its sources — the ITS data model ({@code its.*}),
 * the ranking engine ({@code ranking.*}) and the CLI ({@code rank.*}) — must NOT
 * import anything from the {@code fr.univreunion.bcterm.*} namespace, i.e. the
 * BCTerm bytecode-analysis pipeline this engine was extracted from. Their only
 * couplings are the JDK, Apron and each other, so RaTI stays a self-contained,
 * front-end-agnostic solver that any KoAT producer can reuse.
 *
 * <p>Enforced as a test so a stray {@code import} cannot silently re-couple RaTI
 * to BCTerm (e.g. if the two are later wired together via a git submodule).
 */
public class DecouplingArchitectureTest {

    private static final String[] SOURCE_ROOTS = {
        "src/main/java/fr/univreunion/rati",
    };

    /** RaTI source must not import the BCTerm namespace it was carved out of. */
    private static final Pattern FORBIDDEN = Pattern.compile(
        "^\\s*import\\s+fr\\.univreunion\\.bcterm\\.");

    @Test
    public void engineHasNoBcermDependency() throws IOException {
        List<String> violations = new ArrayList<String>();
        for (String root : SOURCE_ROOTS) {
            Path dir = Paths.get(root);
            if (!Files.isDirectory(dir)) continue;
            try (Stream<Path> files = Files.walk(dir)) {
                for (Path p : (Iterable<Path>) files.filter(f -> f.toString().endsWith(".java"))::iterator) {
                    for (String line : Files.readAllLines(p, StandardCharsets.UTF_8)) {
                        if (FORBIDDEN.matcher(line).find()) {
                            violations.add(p + " : " + line.trim());
                        }
                    }
                }
            }
        }
        assertTrue("RaTI must not import the fr.univreunion.bcterm.* namespace — it is a "
                + "standalone, front-end-agnostic ranking solver. Violations:\n"
                + String.join("\n", violations),
                violations.isEmpty());
    }
}
