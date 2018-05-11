package amalgam.eval.coverage;

import java.io.IOException;
import java.util.List;
import java.util.Map;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;
import edu.mit.csail.sdg.alloy4viz.VizGUI;

public class ModelCLI extends CLI {
    
    
    public static void main(String[] args) throws Err, IOException {
        if (args.length == 0) {
            System.err.println("Usage: ... <file.als> [--model-limit <limit>] [--command <command>]");
            return;
        }
        String filename = args[0];
        Map<String, List<String>> params = parse(args);
        int commandNumber = Integer.parseInt(params.getOrDefault("command", Util.asList("0")).get(0));
        int lim = Integer.parseInt(params.getOrDefault("model-limit", Util.asList("-1")).get(0));
        int symmetry = Integer.parseInt(params.getOrDefault("symmetry", Util.asList("0")).get(0));
        
        A4Reporter rep = new A4Reporter() {
            @Override public void warning(ErrorWarning msg) {
                System.out.print("Relevance Warning:\n"+(msg.toString().trim())+"\n\n");
                System.out.flush();
            }
        };

        System.out.println("=========== Parsing+Typechecking "+filename+" =============");
        Module root = CompUtil.parseEverything_fromFile(rep, null, filename);
        
        Command command = root.getAllCommands().get(commandNumber);
        System.out.println("============ Command "+command+": ============");
        
        A4Options options = new A4Options();
        options.solver = A4Options.SatSolver.MiniSatProverJNI;
        options.noOverflow = true;
        options.inferPartialInstance = false;
        options.skolemDepth = 0; // set to -1 to disable skolemization
        options.symmetry = symmetry;
        
        int i = 1;
        for (A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, root.getAllReachableSigs(), command, options);
             ans.satisfiable() && (i <= lim || lim == -1);
             ans = ans.next()) {
            System.out.println("i = " + i + " model-size: " + ans.eval(Sig.UNIV).size());
            ans.writeXML("/tmp/viz_" + i + ".xml");
            i += 1;
        }
        
        
        while (true) {
            System.out.print("Enter a model number: ");
            new VizGUI(false, "/tmp/viz_" + reader.nextInt() + ".xml", null);
            // viz.loadXML("alloy_example_output.xml", true);
        }
    }
}
