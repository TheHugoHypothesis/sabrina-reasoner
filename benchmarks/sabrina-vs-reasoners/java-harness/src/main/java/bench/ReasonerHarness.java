package bench;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.semanticweb.HermiT.Configuration;
import org.semanticweb.HermiT.ReasonerFactory;
import org.semanticweb.elk.owlapi.ElkReasonerFactory;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.InferenceType;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.*;

/**
 * Fair OWL API 5 benchmark harness for HermiT 1.4.5 and ELK 0.6.0.
 *
 * Reads JSON-line requests from stdin and writes JSON-line responses to stdout.
 * Supports:
 *   - {"cmd": "ping"}
 *   - {"cmd": "query_3val", "reasoner": "hermit"|"elk", "ofn": "...",
 *      "source_iri": "...", "target_iri": "...", "mode": "3val"|"subclass"}
 *   - {"cmd": "session_run", "reasoner": "hermit"|"elk", "tbox_ofn": "...",
 *      "steps": [{"op": "assert"|"retract"|"query", ...}]}
 *   - {"cmd": "quit"}
 */
public class ReasonerHarness {
    private static final Gson GSON = new Gson();

    private static OWLReasoner createReasoner(String name, OWLOntology ont) {
        if ("hermit".equalsIgnoreCase(name)) {
            Configuration cfg = new Configuration();
            cfg.throwInconsistentOntologyException = false;
            OWLReasonerFactory f = new ReasonerFactory();
            return f.createReasoner(ont, cfg);
        } else if ("elk".equalsIgnoreCase(name)) {
            OWLReasonerFactory f = new ElkReasonerFactory();
            return f.createReasoner(ont);
        }
        throw new IllegalArgumentException("Unknown reasoner: " + name);
    }

    private static OWLAxiom parseSingleAxiom(String axiomOfn, String prefixBlock) throws Exception {
        String doc = (prefixBlock == null ? "" : prefixBlock + "\n") + "Ontology(\n  " + axiomOfn + "\n)\n";
        OWLOntologyManager tmpMgr = OWLManager.createOWLOntologyManager();
        OWLOntology tmp = tmpMgr.loadOntologyFromOntologyDocument(
                new ByteArrayInputStream(doc.getBytes(StandardCharsets.UTF_8)));
        Set<OWLAxiom> logical = new LinkedHashSet<>();
        for (OWLAxiom ax : tmp.getAxioms()) {
            if (ax.isLogicalAxiom()) {
                logical.add(ax);
            }
        }
        if (logical.size() != 1) {
            throw new IllegalArgumentException("Expected 1 logical axiom, found " + logical.size() + " in: " + axiomOfn);
        }
        return logical.iterator().next();
    }

    private static String extractPrefixBlock(String ofn) {
        StringBuilder sb = new StringBuilder();
        for (String line : ofn.split("\n")) {
            String t = line.trim();
            if (t.startsWith("Prefix(")) {
                sb.append(t).append("\n");
            }
        }
        return sb.toString();
    }

    private static JsonObject handleQuery3Val(JsonObject req) {
        JsonObject out = new JsonObject();
        String reasonerName = req.get("reasoner").getAsString();
        String ofn = req.get("ofn").getAsString();
        String sourceIri = req.get("source_iri").getAsString();
        String targetIri = req.get("target_iri").getAsString();
        String mode = req.has("mode") ? req.get("mode").getAsString() : "3val";
        boolean precompute = req.has("precompute") && req.get("precompute").getAsBoolean();

        OWLOntologyManager mgr = OWLManager.createOWLOntologyManager();
        OWLDataFactory df = mgr.getOWLDataFactory();
        OWLOntology ont = null;
        OWLReasoner reasoner = null;
        try {
            long t0 = System.nanoTime();
            ont = mgr.loadOntologyFromOntologyDocument(
                    new ByteArrayInputStream(ofn.getBytes(StandardCharsets.UTF_8)));
            long t1 = System.nanoTime();

            reasoner = createReasoner(reasonerName, ont);
            if (precompute) {
                reasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY);
            }
            long t2 = System.nanoTime();

            OWLClass src = df.getOWLClass(IRI.create(sourceIri));
            OWLClass tgt = df.getOWLClass(IRI.create(targetIri));
            OWLSubClassOfAxiom subAx = df.getOWLSubClassOfAxiom(src, tgt);
            OWLDisjointClassesAxiom disjAx = df.getOWLDisjointClassesAxiom(src, tgt);

            boolean consistent = reasoner.isConsistent();
            String verdict;
            boolean subEntailed = false;
            boolean disjEntailed = false;
            if (!consistent) {
                verdict = "INCONSISTENT";
            } else if ("subclass".equalsIgnoreCase(mode)) {
                subEntailed = reasoner.isEntailed(subAx);
                verdict = subEntailed ? "ENTAILED" : "NOT_ENTAILED";
            } else {
                subEntailed = reasoner.isEntailed(subAx);
                if (subEntailed) {
                    verdict = "PROVABLY_TRUE";
                } else {
                    disjEntailed = reasoner.isEntailed(disjAx);
                    verdict = disjEntailed ? "PROVABLY_DISJOINT" : "SENTENCE_INDEPENDENT";
                }
            }
            long t3 = System.nanoTime();

            out.addProperty("ok", true);
            out.addProperty("reasoner", reasonerName);
            out.addProperty("verdict", verdict);
            out.addProperty("consistent", consistent);
            out.addProperty("sub_entailed", subEntailed);
            out.addProperty("disj_entailed", disjEntailed);
            out.addProperty("logical_axioms", ont.getLogicalAxiomCount());
            out.addProperty("parse_ms", (t1 - t0) / 1e6);
            out.addProperty("init_ms", (t2 - t1) / 1e6);
            out.addProperty("query_ms", (t3 - t2) / 1e6);
            out.addProperty("total_ms", (t3 - t0) / 1e6);
        } catch (Throwable ex) {
            out.addProperty("ok", false);
            out.addProperty("reasoner", reasonerName);
            out.addProperty("verdict", "ERROR");
            out.addProperty("error", ex.getClass().getSimpleName() + ": " + ex.getMessage());
        } finally {
            if (reasoner != null) {
                try { reasoner.dispose(); } catch (Throwable ignored) {}
            }
            if (ont != null) {
                try { mgr.removeOntology(ont); } catch (Throwable ignored) {}
            }
        }
        return out;
    }

    private static JsonObject handleBatchOnSameOntology(JsonObject req) {
        JsonObject out = new JsonObject();
        String reasonerName = req.get("reasoner").getAsString();
        String ofn = req.get("ofn").getAsString();
        JsonArray queries = req.getAsJsonArray("queries");
        boolean precompute = !req.has("precompute") || req.get("precompute").getAsBoolean();

        OWLOntologyManager mgr = OWLManager.createOWLOntologyManager();
        OWLDataFactory df = mgr.getOWLDataFactory();
        OWLOntology ont = null;
        OWLReasoner reasoner = null;
        try {
            long t0 = System.nanoTime();
            ont = mgr.loadOntologyFromOntologyDocument(
                    new ByteArrayInputStream(ofn.getBytes(StandardCharsets.UTF_8)));
            long t1 = System.nanoTime();
            reasoner = createReasoner(reasonerName, ont);
            if (precompute) {
                reasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY);
            }
            long t2 = System.nanoTime();

            JsonArray results = new JsonArray();
            long queryTotalNs = 0;
            for (JsonElement el : queries) {
                JsonObject q = el.getAsJsonObject();
                String qid = q.get("id").getAsString();
                String srcIri = q.get("source_iri").getAsString();
                String tgtIri = q.get("target_iri").getAsString();
                String mode = q.has("mode") ? q.get("mode").getAsString() : "3val";

                long qt0 = System.nanoTime();
                OWLClass src = df.getOWLClass(IRI.create(srcIri));
                OWLClass tgt = df.getOWLClass(IRI.create(tgtIri));
                String verdict;
                boolean subEnt = reasoner.isEntailed(df.getOWLSubClassOfAxiom(src, tgt));
                if ("subclass".equalsIgnoreCase(mode)) {
                    verdict = subEnt ? "ENTAILED" : "NOT_ENTAILED";
                } else if (subEnt) {
                    verdict = "PROVABLY_TRUE";
                } else {
                    boolean disjEnt = reasoner.isEntailed(df.getOWLDisjointClassesAxiom(src, tgt));
                    verdict = disjEnt ? "PROVABLY_DISJOINT" : "SENTENCE_INDEPENDENT";
                }
                long qt1 = System.nanoTime();
                queryTotalNs += (qt1 - qt0);

                JsonObject qr = new JsonObject();
                qr.addProperty("id", qid);
                qr.addProperty("verdict", verdict);
                qr.addProperty("query_ms", (qt1 - qt0) / 1e6);
                results.add(qr);
            }

            out.addProperty("ok", true);
            out.addProperty("reasoner", reasonerName);
            out.addProperty("logical_axioms", ont.getLogicalAxiomCount());
            out.addProperty("parse_ms", (t1 - t0) / 1e6);
            out.addProperty("classify_ms", (t2 - t1) / 1e6);
            out.addProperty("queries_total_ms", queryTotalNs / 1e6);
            out.addProperty("total_ms", ((t2 - t0) + queryTotalNs) / 1e6);
            out.add("results", results);
        } catch (Throwable ex) {
            out.addProperty("ok", false);
            out.addProperty("reasoner", reasonerName);
            out.addProperty("error", ex.getClass().getSimpleName() + ": " + ex.getMessage());
        } finally {
            if (reasoner != null) {
                try { reasoner.dispose(); } catch (Throwable ignored) {}
            }
            if (ont != null) {
                try { mgr.removeOntology(ont); } catch (Throwable ignored) {}
            }
        }
        return out;
    }

    private static JsonObject handleSessionRun(JsonObject req) {
        JsonObject out = new JsonObject();
        String reasonerName = req.get("reasoner").getAsString();
        String tboxOfn = req.get("tbox_ofn").getAsString();
        JsonArray steps = req.getAsJsonArray("steps");
        String prefixBlock = extractPrefixBlock(tboxOfn);

        OWLOntologyManager mgr = OWLManager.createOWLOntologyManager();
        OWLOntology ont = null;
        OWLReasoner reasoner = null;
        Map<String, OWLAxiom> facts = new HashMap<>();

        try {
            long t0 = System.nanoTime();
            ont = mgr.loadOntologyFromOntologyDocument(
                    new ByteArrayInputStream(tboxOfn.getBytes(StandardCharsets.UTF_8)));
            reasoner = createReasoner(reasonerName, ont);
            reasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY, InferenceType.CLASS_ASSERTIONS);
            long t1 = System.nanoTime();

            JsonArray stepResults = new JsonArray();
            long stepsTotalNs = 0;

            for (JsonElement el : steps) {
                JsonObject st = el.getAsJsonObject();
                String op = st.get("op").getAsString();
                JsonObject sr = new JsonObject();
                sr.addProperty("op", op);

                long st0 = System.nanoTime();
                if ("assert".equalsIgnoreCase(op)) {
                    String fid = st.get("id").getAsString();
                    OWLAxiom ax = parseSingleAxiom(st.get("ofn").getAsString(), prefixBlock);
                    facts.put(fid, ax);
                    mgr.addAxiom(ont, ax);
                    reasoner.flush();
                    sr.addProperty("id", fid);
                } else if ("retract".equalsIgnoreCase(op)) {
                    String fid = st.get("id").getAsString();
                    OWLAxiom ax = facts.remove(fid);
                    if (ax != null) {
                        mgr.removeAxiom(ont, ax);
                        reasoner.flush();
                    }
                    sr.addProperty("id", fid);
                } else if ("query".equalsIgnoreCase(op)) {
                    OWLAxiom qAx = parseSingleAxiom(st.get("ofn").getAsString(), prefixBlock);
                    boolean ent = reasoner.isEntailed(qAx);
                    sr.addProperty("verdict", ent ? "ENTAILED" : "NOT_ENTAILED");
                }
                long st1 = System.nanoTime();
                stepsTotalNs += (st1 - st0);
                sr.addProperty("ms", (st1 - st0) / 1e6);
                stepResults.add(sr);
            }

            out.addProperty("ok", true);
            out.addProperty("reasoner", reasonerName);
            out.addProperty("load_ms", (t1 - t0) / 1e6);
            out.addProperty("steps_ms", stepsTotalNs / 1e6);
            out.addProperty("total_ms", ((t1 - t0) + stepsTotalNs) / 1e6);
            out.add("step_results", stepResults);
        } catch (Throwable ex) {
            out.addProperty("ok", false);
            out.addProperty("reasoner", reasonerName);
            out.addProperty("error", ex.getClass().getSimpleName() + ": " + ex.getMessage());
        } finally {
            if (reasoner != null) {
                try { reasoner.dispose(); } catch (Throwable ignored) {}
            }
            if (ont != null) {
                try { mgr.removeOntology(ont); } catch (Throwable ignored) {}
            }
        }
        return out;
    }

    public static void main(String[] args) throws Exception {
        boolean oneshot = args.length > 0 && "--oneshot".equals(args[0]);
        BufferedReader br = new BufferedReader(new InputStreamReader(System.in, StandardCharsets.UTF_8));
        String line;
        while ((line = br.readLine()) != null) {
            String trimmed = line.trim();
            if (trimmed.isEmpty()) continue;
            JsonObject req = JsonParser.parseString(trimmed).getAsJsonObject();
            String cmd = req.get("cmd").getAsString();
            if ("quit".equalsIgnoreCase(cmd)) {
                JsonObject bye = new JsonObject();
                bye.addProperty("ok", true);
                System.out.println(GSON.toJson(bye));
                System.out.flush();
                break;
            }
            JsonObject resp;
            if ("ping".equalsIgnoreCase(cmd)) {
                resp = new JsonObject();
                resp.addProperty("ok", true);
                resp.addProperty("java", System.getProperty("java.version"));
            } else if ("query_3val".equalsIgnoreCase(cmd)) {
                resp = handleQuery3Val(req);
            } else if ("batch_same_ontology".equalsIgnoreCase(cmd)) {
                resp = handleBatchOnSameOntology(req);
            } else if ("session_run".equalsIgnoreCase(cmd)) {
                resp = handleSessionRun(req);
            } else {
                resp = new JsonObject();
                resp.addProperty("ok", false);
                resp.addProperty("error", "Unknown command: " + cmd);
            }
            System.out.println(GSON.toJson(resp));
            System.out.flush();
            if (oneshot) break;
        }
    }
}
