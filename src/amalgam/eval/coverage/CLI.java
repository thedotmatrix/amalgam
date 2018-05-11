package amalgam.eval.coverage;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Scanner;

public class CLI {
    static Map<String, List<String>> parse(String[] args) throws IOException {
        Map<String, List<String>> params = new HashMap<>();
        List<String> options = null;
        for (int i = 1; i < args.length; i++) {
            final String a = args[i];
            if (a.startsWith("--")) {
                options = new ArrayList<>();
                params.put(a.substring(2), options);
            } else if (options != null) {
                options.add(a);
            } else {
                throw new IOException("Illegal parameter usage");
            }
        }
        return params;
    }
    
    static Scanner reader = new Scanner(System.in);
    
    
}

