/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.alloy4compiler.ast;

import java.util.List;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Pos;

/** Immutable; this declaration binds a list of names to an expression. */

public final class Decl implements Comparable<Decl> {

    /** If nonnull, then this decl is private (and this.isPrivate is the location of the "private" keyword) */
    public final Pos isPrivate;

    /** If nonnull, then each name is disjoint (and this.disjoint is the location of the "disjoint" keyword) */
    public final Pos disjoint;

    /** If nonnull, then each atom of this sig has disjoint value for this field (and this.disjoint2 is the location of the "disjoint" keyword) */
    public final Pos disjoint2;

    /** The list of names. */
    public final ConstList<? extends ExprHasName> names;

    /** The value that the list of names are bound to. */
    public final Expr expr;

    /** Caches the span() result. */
    private Pos span;
    
    @Override
    public int compareTo(Decl o) {
        int result = 0;
        if (isPrivate != null) {
            result = isPrivate.compareTo(o.isPrivate);
            if (result != 0) return result;
        }
        if (disjoint != null) {
            result = disjoint.compareTo(o.disjoint);
            if (result != 0) return result;
        }
        if (disjoint2 != null) {
            result = disjoint2.compareTo(o.disjoint2);
            if (result != 0) return result;
        }
        
        for (int i = 0; i < names.size(); i++) {
            result = names.get(i).compareTo(o.names.get(i));
            if (result != 0) return result;
        }
        return expr.compareTo(o.expr);
    }

    /** Returns a Pos object representing the entire span of this expression and all its subexpressions. */
    public Pos span() {
       Pos p = span;
       if (p == null) {
          p = expr.span().merge(disjoint).merge(disjoint2);
          for(ExprHasName n: names) p = p.merge(n.span());
          span = p;
       }
       return p;
    }

    /** This constructs a declaration; the list of names must not be empty. */
    public Decl(Pos isPrivate, Pos disjoint, Pos disjoint2, List<? extends ExprHasName> names, Expr expr) {
       if (names.size()==0) throw new NullPointerException();
       this.isPrivate = isPrivate;
       this.disjoint = (names.size()>1 ? disjoint : null);
       this.disjoint2 = disjoint2;
       this.names = ConstList.make(names);
       this.expr = expr;
    }

    /** Return the first variable in this declaration. */
    public ExprHasName get() {
       return names.get(0);
    }

    /** If the list of declaration contains a duplicate name, return one such duplicate name, else return null. */
    public static ExprHasName findDuplicateName (List<Decl> list) {
       for(int i=0; i<list.size(); i++) {
          Decl d=list.get(i);
          for(int j=0; j<d.names.size(); j++) {
             ExprHasName n = d.names.get(j);
             for(int k=j+1; k<d.names.size(); k++) if (d.names.get(k).label.equals(n.label)) return n;
             for(int k=i+1; k<list.size(); k++) if (list.get(k).hasName(n.label)) return n;
          }
       }
       return null;
    }

    /** Returns true if this declaration contains the given name. */
    public boolean hasName(String name) {
       for(int i=0; i<names.size(); i++) if (names.get(i).label.equals(name)) return true;
       return false;
    }
    
    // TN AMALGAM: largely leaving Eclipse's generated functions intact, but cache.
    // Note that we need to leave span() in the hashcode/equals, since we use source loc
    // (likely OK to collapse different locs for SOME applications, but not all)
    private int hashCache = 0;
    private boolean hashCached = false;
    
    public int spanIndependentHashCode() {
        if(hashCached) return hashCache;
        final int prime = 31;
        int result = 1;
        result = prime * result + ((disjoint == null) ? 1 : 5);
        result = prime * result + ((disjoint2 == null) ? 1 : 5);
        result = prime * result + ((expr == null) ? 0 : expr.spanIndependentHashCode());
        result = prime * result + ((isPrivate == null) ? 1 : 5);
        result = prime * result + ((names == null) ? 0 : names.spanIndependentHashCode());
        // Remember to use span() not span. 
       // result = prime * result + ((span() == null) ? 0 : span().hashCode());
        hashCache = result;
        hashCached = true;  
        return result;
    }
    
    public boolean spanIndependentEquals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        Decl other = (Decl) obj;
        
        if (disjoint == null && other.disjoint != null) return false;
        if (disjoint != null && other.disjoint == null) return false;
        
        if (disjoint2 == null && other.disjoint2 != null) return false;
        if (disjoint2 != null && other.disjoint2 == null) return false;        
        
        if (expr == null) {
            if (other.expr != null)
                return false;
        } else if (!expr.spanIndependentEquals(other.expr))
            return false;
        
        if (isPrivate == null && other.isPrivate != null) return false;
        if (isPrivate != null && other.isPrivate == null) return false;
        
        if (names == null) {
            if (other.names != null)
                return false;
        } else if (!names.spanIndependentEquals(other.names))
            return false;
        
        // Remember to use span() not span. 
        //if (span() == null) {
        //    if (other.span() != null)
        //        return false;
        //} else if (!span().equals(other.span()))
        //    return false;
        return true;
    }  
    
}
