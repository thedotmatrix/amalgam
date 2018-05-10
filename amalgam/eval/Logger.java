package eval;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.nio.file.Files;
import java.util.Arrays;

import edu.mit.csail.sdg.alloy4whole.SimpleGUI;

public final class Logger {
    private static final boolean log = true; // Please don't commit a false value!
    private static final String fs = System.getProperty("file.separator");
    private static final String file = SimpleGUI.alloyHome() + fs + "LOG.csv";
    private static final String cs = ", ";
    private static Long start; // start of logging

    public static String currentLog() {
        String oldlog = "";
        if(new File(file).exists()) {
            try {
                oldlog = new String(Files.readAllBytes(new File(file).toPath()));
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
        return oldlog;
    }
    
    private static void update(String newline) {
            // Check for old log
            String oldlog = currentLog();
            // write out log
            PrintWriter out;
            try {
                out = new PrintWriter(file, "UTF-8");
                out.print(oldlog);
                out.println(newline);
                out.flush();
                out.close();
            } catch (FileNotFoundException e) {
                e.printStackTrace();
            } catch (UnsupportedEncodingException e) {
                e.printStackTrace();
            }
    }

    public static enum Event {
        OPEN,
        SAVE,
        CLOS,
        OPTS,
        EXEC,
        CORE,
        SHOW,
        NEXT,
        EVAL
    }
    
    public static void log(Event e, String ... args) {
        if(log) {
            if(start == null) start = System.currentTimeMillis();
            String logline = (System.currentTimeMillis()-start)+cs+e.name();
            for(String arg : Arrays.asList(args)) {
                logline += cs+"\""+arg+"\"";
            }
            update(logline);
        }
    }
}
