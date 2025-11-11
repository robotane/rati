package fr.univreunion.rati.rank;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import org.junit.Test;

import fr.univreunion.rati.ranking.FarkasRanking;
import fr.univreunion.rati.ranking.NonTermination;

/**
 * End-to-end non-termination run: parse a real KoAT file and get a verified
 * NONTERMINATES with its recurrent-set witness. The bundled example diverges
 * because the b_2 ↔ b_3 loop increments LI3 forever once SI0 (= LI3, set to 10
 * before the loop) stays ≥ 1.
 */
public class NonTerminationE2ETest {

    @Test
    public void bundledNonterminatingExample_disproved() throws Exception {
        Path file = Paths.get("examples", "nonterminating.koat");
        String text = new String(Files.readAllBytes(file), StandardCharsets.UTF_8);
        KoatParser.Parsed parsed = KoatParser.parse(text);

        FarkasRanking.Certificate cert =
                FarkasRanking.proveWithCertificate(parsed.its, parsed.start);
        assertEquals(FarkasRanking.Verdict.NONTERMINATES, cert.verdict);

        NonTermination.Witness w = cert.nonTermination;
        assertNotNull(w);
        assertFalse(w.recurrentSet.isEmpty());
        assertFalse(w.cycle.isEmpty());
        // The looping SCC is b_2 ↔ b_3, far from the entry: a non-empty path is needed.
        assertFalse(w.path.isEmpty());
        assertEquals(parsed.start, w.path.get(0).source().name());
    }
}
