import org.semanticweb.HermiT.ReasonerFactory;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.StringDocumentSource;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.profiles.OWL2DLProfile;
import org.semanticweb.owlapi.profiles.OWLProfileReport;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import openllet.owlapi.OpenlletReasonerFactory;
import uk.ac.manchester.cs.jfact.JFactFactory;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.concurrent.*;

public class BoundaryAudit {
  private static String runTimed(Callable<String> task, int timeoutSec) {
    ExecutorService ex = Executors.newSingleThreadExecutor();
    Future<String> f = ex.submit(task);
    try {
      return f.get(timeoutSec, TimeUnit.SECONDS);
    } catch (TimeoutException te) {
      f.cancel(true);
      return "TIMEOUT";
    } catch (ExecutionException ee) {
      Throwable c = ee.getCause();
      String msg = c.getMessage() == null ? "" : c.getMessage().replace("\n", " ").replace("\"", "'");
      return "EXCEPTION:" + c.getClass().getSimpleName() + ":" + msg;
    } catch (Exception e) {
      return "ERROR:" + e.getMessage();
    } finally {
      ex.shutdownNow();
    }
  }

  private static String esc(String s) {
    return s.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", " ");
  }

  public static void main(String[] args) throws Exception {
    if (args.length < 1) {
      System.err.println("Usage: BoundaryAudit <ofn-file>");
      System.exit(1);
    }
    String ofn = Files.readString(Path.of(args[0]));
    OWLOntologyManager m = OWLManager.createOWLOntologyManager();
    OWLOntology ont = m.loadOntologyFromOntologyDocument(new StringDocumentSource(ofn));
    OWLProfileReport rep = new OWL2DLProfile().checkOntology(ont);

    String hermit = runTimed(() -> {
      OWLReasoner r = new ReasonerFactory().createReasoner(ont);
      boolean c = r.isConsistent();
      r.dispose();
      return c ? "CONSISTENT" : "INCONSISTENT";
    }, 10);

    String openllet = runTimed(() -> {
      OWLReasoner r = OpenlletReasonerFactory.getInstance().createReasoner(ont);
      boolean c = r.isConsistent();
      r.dispose();
      return c ? "CONSISTENT" : "INCONSISTENT";
    }, 10);

    String jfact = runTimed(() -> {
      OWLReasoner r = new JFactFactory().createReasoner(ont);
      boolean c = r.isConsistent();
      r.dispose();
      return c ? "CONSISTENT" : "INCONSISTENT";
    }, 10);

    System.out.printf(
        "{\"owlapi_in_profile\":%s,\"owlapi_violations\":%d,\"hermit\":\"%s\",\"openllet\":\"%s\",\"jfact\":\"%s\"}%n",
        rep.isInProfile(), rep.getViolations().size(), esc(hermit), esc(openllet), esc(jfact));
  }
}
