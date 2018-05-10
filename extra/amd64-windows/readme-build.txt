Built via MinGW (it's vital to use the 64-bit version). Be sure to include 'MINGW' in defines, or else 
minisat tries to use sys/resources.h, which is not available on Windows. 

By default, the file would depend on another dll: libstdc++-6.dll. 
We would then have to load *BOTH* DLLs explicitly in both the UI and worker process.

Instead, use the "-static-libstdc++" and "-static-libgcc" options to remove this dependency.

Note: Tim had to rename his jvm.dll in order to make the Kodkod waf script find jvm.lib.