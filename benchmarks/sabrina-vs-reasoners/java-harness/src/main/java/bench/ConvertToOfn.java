package bench;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.formats.FunctionalSyntaxDocumentFormat;
import org.semanticweb.owlapi.model.*;

import java.io.File;
import java.io.FileOutputStream;
import java.util.*;

/**
 * Converts an OWL ontology (RDF/XML, OBO, etc.) to a clean logical-only W3C
 * OWL 2 Functional-Style Syntax (.ofn) document (preserving 100% of OWL 2 DL
 * logical axioms and declarations while stripping annotation axioms and non-DL
 * SWRL rules). Prints JSON stats to stdout.
 */
public class ConvertToOfn {
    public static void main(String[] args) throws Exception {
        if (args.length < 2) {
            System.err.println("Usage: ConvertToOfn <input.owl> <output.ofn>");
            System.exit(2);
        }
        File inFile = new File(args[0]);
        File outFile = new File(args[1]);

        OWLOntologyManager mgr = OWLManager.createOWLOntologyManager();
        OWLOntologyLoaderConfiguration cfg = new OWLOntologyLoaderConfiguration()
                .setMissingImportHandlingStrategy(MissingImportHandlingStrategy.SILENT);
        OWLOntology src = mgr.loadOntologyFromOntologyDocument(
                new org.semanticweb.owlapi.io.FileDocumentSource(inFile), cfg);

        OWLOntologyManager outMgr = OWLManager.createOWLOntologyManager();
        IRI ontIri = src.getOntologyID().getOntologyIRI().orElse(IRI.create("urn:bench:" + outFile.getName()));
        OWLOntology dst = outMgr.createOntology(ontIri);

        int logicalKept = 0;
        int swrlSkipped = 0;
        int declKept = 0;
        for (OWLAxiom ax : src.getAxioms()) {
            if (ax instanceof SWRLRule) {
                swrlSkipped++;
                continue;
            }
            if (ax.isLogicalAxiom()) {
                outMgr.addAxiom(dst, ax);
                logicalKept++;
            } else if (ax instanceof OWLDeclarationAxiom) {
                outMgr.addAxiom(dst, ax);
                declKept++;
            }
        }

        FunctionalSyntaxDocumentFormat fmt = new FunctionalSyntaxDocumentFormat();
        try (FileOutputStream fos = new FileOutputStream(outFile)) {
            outMgr.saveOntology(dst, fmt, fos);
        }

        System.out.printf(
                "{\"input\":\"%s\",\"output\":\"%s\",\"logical_axioms\":%d,\"declarations\":%d,\"classes\":%d,\"obj_props\":%d,\"swrl_skipped\":%d}%n",
                inFile.getName(),
                outFile.getName(),
                logicalKept,
                declKept,
                dst.getClassesInSignature().size(),
                dst.getObjectPropertiesInSignature().size(),
                swrlSkipped
        );
    }
}
