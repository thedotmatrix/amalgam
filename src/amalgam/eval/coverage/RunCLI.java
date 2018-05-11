package amalgam.eval.coverage;

import java.io.IOException;
import java.util.List;
import java.util.Map;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.ProvenanceTraceWrapper;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;
import edu.mit.csail.sdg.alloy4whole.CoverageOptions;
import edu.mit.csail.sdg.alloy4whole.CoverageTextLog;
import edu.mit.csail.sdg.alloy4whole.CoverageUI;

public class RunCLI extends CLI {
    public static void main(String[] args) throws Err, IOException {
        if (args.length == 0) {
            System.err.println("Usage: ... <file.als>\n");
            return;
        }
        
        
        String filename = args[0];
        Map<String, List<String>> params = parse(args);
        
        CoverageOptions cOptS = new CoverageOptions();
        cOptS.modelLimit = -1;
        cOptS.satTrick = true;
        cOptS.inclusive = true;
        
        CoverageOptions cOptN = cOptS.dup();
        cOptN.satTrick = false;

        A4Reporter rep = new A4Reporter();
        System.out.println("=========== Parsing+Typechecking "+filename+" =============");
        Module root = CompUtil.parseEverything_fromFile(rep, null, filename);
        
        Command command = root.getAllCommands().get(Integer.parseInt(params.getOrDefault("command", Util.asList("0")).get(0)));
        System.out.println("============ Command "+command+": ============");
        
        A4Options options = new A4Options();
        options.solver = A4Options.SatSolver.MiniSatProverJNI;
        options.noOverflow = true;
        options.inferPartialInstance = false;
        options.skolemDepth = -1; // set to -1 to disable skolemization
        options.symmetry = 2000;
        
        CoverageUI cEngineN = new CoverageUI(root, null, new CoverageTextLog(), null);
        CoverageUI cEngineB = new CoverageUI(root, null, new CoverageTextLog(), null);
        
        List<ProvenanceTraceWrapper> csN = cEngineN.justFind(
                TranslateAlloyToKodkod.execute_command(rep, root.getAllReachableSigs(), command, options),
                cOptS);
        
        List<ProvenanceTraceWrapper> csB = cEngineB.justFind(
                TranslateAlloyToKodkod.execute_command(rep, root.getAllReachableSigs(), command, options),
                cOptN);
        
        if (csN.size() != csB.size()) {
            throw new ErrorFatal("asd");
        }
        
        
        csN.removeAll(csB);
        
        if (!csN.isEmpty()) throw new ErrorFatal("asd2");
        System.out.println(csB);
    }

}