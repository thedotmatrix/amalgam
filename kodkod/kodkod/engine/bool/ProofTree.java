package kodkod.engine.bool;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import kodkod.ast.Node;
import kodkod.engine.Translate;
import kodkod.engine.bool.Operator.Nary;
import kodkod.engine.satlab.Clause;
import kodkod.engine.satlab.ResolutionTrace;
import kodkod.util.ints.IntIterator;

public class ProofTree {
	public BooleanFormula original;
	// Set of "and" children. ("or" is represented via separate trees)
	public Set<ProofTree> children; 

	// Every proof tree has a set of commitments: the disjuncts it's taken for a particular positive-implication-form clause.
	public Map<List<Integer>, Integer> choices = new HashMap<List<Integer>, Integer>();

	// Assume tree is complete unless it or one of its children is flagged otherwise in search
	public boolean complete = true;

	public int rootLiteral;

	enum Flag {START_CYCLE, DEFINITE_IMPLICATION, NO_EXPLANATION, UNFINISHED, ERROR};
	Set<Flag> flags = new HashSet<Flag>();

	public Set<Integer> indefiniteOptions = new HashSet<Integer>();

	// new constructor
	public ProofTree(Translate translate, Map<Integer, BooleanFormula> sVarFolder, int[] root) {
		// build root clause
		BooleanAccumulator clause =  BooleanAccumulator.treeGate(Nary.OR);
		for(int i=0;i<root.length;i++) {
			int v = root[i];
			boolean neg = v<0;
			v = Math.abs(v);
			// TODO when to unfold and when not to unfold
			BooleanFormula vFold = sVarFolder.containsKey(v) && !translate.svm.containsKey(v) ? sVarFolder.get(v) : new BooleanVariable(v);
			vFold = neg ? new NotGate(vFold) : vFold;
			clause.add(vFold);
			if(i==0) rootLiteral = root[i];
		}
		this.original = new NaryGate(clause, -1, clause.hashCode());
		children = new HashSet<>();
	}
	// copy constructor
	public ProofTree(ProofTree toCopy) {
		this.rootLiteral = toCopy.rootLiteral;
		this.original = toCopy.original;
		this.flags = toCopy.flags;
		this.children = new HashSet<>();			
		for(ProofTree child : children) {
			this.children.add(new ProofTree(child));

			for(List<Integer> cl: child.choices.keySet()) { 
				this.addChoice(cl, child.choices.get(cl)); 
			}						
			this.complete &= child.complete;
		}
	}
	/* construction */
	//public class ProofTreeException extends Exception {
	//		ProofTreeException(String msg) {
	//		super(msg);
	//	}
	//}
	public boolean compatibleChoices(ProofTree other) {
		for(List<Integer> cl : other.choices.keySet()) {
			if(choices.containsKey(cl) && other.choices.get(cl) != this.choices.get(cl)) {
				return false;
			}
		}
		return true;
	}
	public void addChoice(List<Integer> cl, Integer choice) {		
		if(choices.containsKey(cl) && choices.get(cl) != choice) {
			//throw new ProofTreeException("incompatable choice: "+cl+" "+choices.get(cl)+" "+choice);
			System.err.println("ERROR: incompatable choice: "+cl+" "+choices.get(cl)+" "+choice+"\n\n");
			System.err.println("Choices so far:"+choices);
			throw new Error("fail!");
		}
		// no harm re-adding same value
		//if(choices.containsKey(cl)) {
		//System.err.println("DEBUG: choice already present: "+cl+" "+choices.get(cl)+" "+choice+"\n\n");
		//}
		//System.err.println("choice: "+cl+" "+" "+choice);
		choices.put(cl, choice);	
	}	
	public boolean addChild(ProofTree child) {
		// Parent reflects the clause-use commitments made by children
		for(List<Integer> cl : child.choices.keySet()) {
			addChoice(cl, child.choices.get(cl));			
		}
		//System.err.println("Added child. New choice set: "+choices);
		// finally, add the child				
		this.complete &= child.complete;		
		return children.add(child);
	}
	public boolean addChildUnique(ProofTree child) {
		// Test to make sure we don't have a direct child with this literal already
		for(ProofTree otherchild : children) {
			if(otherchild.rootLiteral == child.rootLiteral) 
				return false;
		}
		return addChild(child);
	}
	public static Clause findResolvant(ResolutionTrace t, Clause root) {
		IntIterator itr = t.resolvents().iterator();
		while(itr.hasNext()) {
			Clause resolve = t.get(itr.next());
			if(Translate.clauseEqual(resolve, root)) return resolve;
		}
		return null;
	}
	public static ProofTree build(Translate translate, Map<Integer, BooleanFormula> sVarFolder, ResolutionTrace trace, Clause root, List<Clause> visited) {
		ProofTree tree = new ProofTree(translate, sVarFolder, root.toArray());
		Iterator<Clause> children = root.antecedents();
		visited.add(root);
		while(children.hasNext()) {
			Clause child = children.next();
			boolean isVisited = false;
			for(Clause v : visited) {
				isVisited |= Translate.clauseEqual(child, v);
			}
			// if it's a resolvant itself, build the whole tree
			Clause childroot = findResolvant(trace, child);
			if(childroot!=null && !isVisited) {
				tree.addChild(build(translate, sVarFolder, trace, childroot, visited));
			} 
			// if it's just an axiom, add the flat clause
			else {
				tree.addChild(new ProofTree(translate, sVarFolder, child.toArray()));
			}
		}
		return tree;
	}
	/* prints */
	public String printOriginal(String tabs) {
		String out = tabs+this.original;
		if(flags.contains(Flag.ERROR)) out += " <<<ERROR>>>";
		else if(flags.contains(Flag.NO_EXPLANATION)) out += " <<<no explanation>>>";
		else if(flags.contains(Flag.UNFINISHED)) out += " <<<UNFINISHED>>>";
		else if(flags.contains(Flag.START_CYCLE)) out += " <<<cycle>>>";						
		else if(!flags.contains(Flag.DEFINITE_IMPLICATION)) out += " <<<INDEFINITE: "+indefiniteOptions+">>>";	
		out += "\n";
		for(ProofTree child : children) {
			out += child.printOriginal(tabs+"\t");
		}
		return out;
	}
	public String printLiterals(String tabs) {
		String out = tabs+this.rootLiteral;
		if(flags.contains(Flag.ERROR)) out += " <<<ERROR>>>";
		else if(flags.contains(Flag.NO_EXPLANATION)) out += " <<<no explanation>>>";
		else if(flags.contains(Flag.UNFINISHED)) out += " <<<UNFINISHED>>>";
		else if(flags.contains(Flag.START_CYCLE)) out += " <<<cycle>>>";						
		else if(!flags.contains(Flag.DEFINITE_IMPLICATION)) out += " <<<INDEFINITE: "+indefiniteOptions+">>>";	
		out += "\n";
		for(ProofTree child : children) {
			out += child.printLiterals(tabs+"\t");
		}
		return out;
	}
	public String printTranslated(Translate translate, String tabs) {
		String out = tabs;
		out += this.original.accept(new BooleanTranslator(false), translate);
		if(flags.contains(Flag.ERROR)) out += " <<<ERROR>>>";
		else if(flags.contains(Flag.NO_EXPLANATION)) out += " <<<no explanation>>>";
		else if(flags.contains(Flag.UNFINISHED)) out += " <<<UNFINISHED>>>";
		else if(flags.contains(Flag.START_CYCLE)) out += " <<<cycle>>>";						
		else if(!flags.contains(Flag.DEFINITE_IMPLICATION)) out += " <<<INDEFINITE: "+indefiniteOptions+">>>";
		out += "\n";
		for(ProofTree child : children) {
			out += child.printTranslated(translate, tabs+"\t");
		}
		return out;
	}
	private Map<Integer, String> treeLiterals(Map<Integer, String> lits, Translate translate, boolean p, boolean s, boolean t) {
		boolean takePrimary = p&&translate.isPrimary(this.rootLiteral);
		boolean takeSecondary = s&&translate.isSecondary(this.rootLiteral);
		if(takePrimary||takeSecondary||t) lits.put(this.rootLiteral, translate.varToString(rootLiteral));
		for(ProofTree child : this.children) {
			child.treeLiterals(lits, translate, p, s, t);
		}
		return lits;
	}
	public Map<Integer, String> treeLiterals(Translate translate, boolean p, boolean s, boolean t) {
		Map<Integer, String> lits = new HashMap<>();
		treeLiterals(lits, translate, p, s, t);
		return lits; 
	}
	public LinkedHashSet<Node> pCore(Translate translate) {
		return translate.pCore(treeLiterals(translate, true, true, true).keySet());
	}
	private class GraphNode {
		static final int PP = 101;
		static final int PS = 102;
		static final int PT = 103;
		static final int NP = 111;
		static final int NS = 112;
		static final int NT = 113;
		String translation;
		int id; 
		int pID; 
		Set<Flag> flags;
		GraphNode(ProofTree p, BooleanTranslator trans, Translate translate) {
			this.translation = p.original.accept(trans, translate);
			if(translation.length()>42) translation = translation.substring(0, 42)+"...";
			boolean isPositive = p.rootLiteral>0;
			boolean isPrimary = translate.isPrimary(p.rootLiteral);
			boolean isSecondary = translate.isTopLevelSecondary(p.rootLiteral);
			if(isPrimary) {
				this.pID = isPositive ? GraphNode.PP : GraphNode.NP;
			} else if (isSecondary) {
				this.pID = isPositive ? GraphNode.PS : GraphNode.NS;
			} else {
				this.pID = isPositive ? GraphNode.PT : GraphNode.NT;
			}
			this.id = p.rootLiteral;
			this.flags = p.flags;
		}
		@Override
		public boolean equals(Object o) {
			boolean eq = false;
			if(o instanceof GraphNode) {
				GraphNode other = (GraphNode)o;
				eq = Integer.compare(this.id, other.id)==0;
			}
			return eq;
		}
		@Override
		public int hashCode() {
			return id;
		}
	}
	void buildGraph(Map<GraphNode, Set<GraphNode>> graph, BooleanTranslator trans, Translate translate) {
		Set<GraphNode> childs = new HashSet<>();
		for(ProofTree child : this.children) {
			childs.add(new GraphNode(child, trans, translate));
			child.buildGraph(graph, trans, translate);
		}
		graph.put(new GraphNode(this, trans, translate), childs);
	}
	public String printXMLTree(Translate translate, Map<Object, String> atom2name) {
		int i = 1000;
		Map<GraphNode, Set<GraphNode>> graph = new HashMap<>();
		translate.atom2name = atom2name;
		buildGraph(graph, new BooleanTranslator(true), translate);

		// header
		String out = "<alloy builddate=\"Not a real date\">\n"+
				"\t<instance bitwidth=\"0\" maxseq=\"0\" command=\"Proof Tree\" filename=\"\">\n"+
				"\t\t<sig label=\"univ\" ID=\"2\" builtin=\"yes\"></sig>\n"+
				"\t\t<sig label=\"seq/Int\" ID=\"0\" parentID=\"1\" builtin=\"yes\"></sig>\n"+
				"\t\t<sig label=\"Int\" ID=\"1\" parentID=\"2\" builtin=\"yes\"></sig>\n"+
				"\t\t<sig label=\"PP\" ID=\""+GraphNode.PP+"\" parentID=\"100\"></sig>\n"+
				"\t\t<sig label=\"PS\" ID=\""+GraphNode.PS+"\" parentID=\"100\"></sig>\n"+
				"\t\t<sig label=\"PT\" ID=\""+GraphNode.PT+"\" parentID=\"100\"></sig>\n"+
				"\t\t<sig label=\"NP\" ID=\""+GraphNode.NP+"\" parentID=\"100\"></sig>\n"+
				"\t\t<sig label=\"NS\" ID=\""+GraphNode.NS+"\" parentID=\"100\"></sig>\n"+
				"\t\t<sig label=\"NT\" ID=\""+GraphNode.NT+"\" parentID=\"100\"></sig>\n"+
				"\t\t<sig label=\"NODE\" ID=\"100\" parentID=\"2\"></sig>\n";

		// string sig
		out += "\t\t<sig label=\"String\" ID=\"3\" parentID=\"2\" builtin=\"yes\">\n";
		for(GraphNode key : graph.keySet()) {
			out +=  "\t\t\t<atom label=\""+key.translation+"\"/>\n";
			out +=  "\t\t\t<atom label=\""+key.flags+"\"/>\n";
		}
		out += "\t\t</sig>\n";
		// node sig
		for(GraphNode key : graph.keySet()) {
			out +=  "\t\t<sig label=\""+key.id+"\" ID=\""+(i++)+"\" parentID=\""+key.pID+"\">\n"+
					"\t\t\t<atom label=\""+key.id+"\"/>\n"+
					"\t\t</sig>\n";
		}

		// edge field
		out += "\t\t<field label=\" \" ID=\"99\" parentID=\"100\">\n";
		for(GraphNode cons : graph.keySet()) {
			for(GraphNode ante : graph.get(cons)) {
				out += "\t\t\t<tuple> <atom label=\""+
						ante.id+
						"\"/> <atom label=\""+
						cons.id+
						"\"/> </tuple>\n";
			}
		}
		out += "\t\t\t<types> <type ID=\"100\"/> <type ID=\"100\"/> </types>\n"+
				"\t\t</field>\n";

		// translation field
		out += "\t\t<field label=\"Fact\" ID=\"98\" parentID=\"100\">\n";
		for(GraphNode node : graph.keySet()) {
			out += "\t\t\t<tuple> <atom label=\""+
					node.id+
					"\"/> <atom label=\""+
					node.translation+
					"\"/> </tuple>\n";
		}
		out += "\t\t\t<types> <type ID=\"100\"/> <type ID=\"3\"/> </types>\n"+
				"\t\t</field>\n";

		// flags field
		out += "\t\t<field label=\"Flags\" ID=\"97\" parentID=\"100\">\n";
		for(GraphNode node : graph.keySet()) {
			out += "\t\t\t<tuple> <atom label=\""+
					node.id+
					"\"/> <atom label=\""+
					node.flags+
					"\"/> </tuple>\n";
		}
		out += "\t\t\t<types> <type ID=\"100\"/> <type ID=\"3\"/> </types>\n"+
				"\t\t</field>\n";

		// footer
		out +=  "\t</instance>\n"+
				"\t<source filename=\"notareal.file\" content=\"\" />\n"+
				"</alloy>\n\n\n";
		return out;
	}
	/* reduction */
	public void removeTriggers(Set<Integer> triggers) {
		Set<Integer> removed = new HashSet<>();
		this.original = this.original.accept(new UnitProper(triggers), removed);
		for(ProofTree child : this.children) {
			child.removeTriggers(triggers);
		}
	}
	public void pushNegation() {
		this.original = this.original.accept(new NegationPusher(), false);
		for(ProofTree child : this.children) {
			child.pushNegation();
		}
	}

	public void addFlag(Flag f) {
		flags.add(f);
	}
	public void removeFlag(Flag f) {
		flags.remove(f);
	}
	@Override
	public boolean equals(Object o) {
		boolean eq = false;
		if(o instanceof ProofTree) {
			ProofTree other = (ProofTree)o;
			eq = this.original.equals(other.original) 
					&& this.children.equals(other.children);
		}
		return eq;
	}
}


/*******************************************************************************
 * Converts propositional formulas into first order strings
 ******************************************************************************/
class BooleanTranslator implements BooleanVisitor<String, Translate>  {
	boolean alloynames;
	public BooleanTranslator(boolean alloynames) {
		this.alloynames = alloynames; 
	}
	@Override
	public String visit(MultiGate multigate, Translate translate) {
		String out = "(";
		Iterator<BooleanFormula> itr = multigate.iterator();
		while(itr.hasNext()) {
			BooleanFormula fml = itr.next();
			out += fml.accept(this, translate);
			out += multigate.op();
		}
		if(multigate.size()>0) out = out.substring(0, out.length()-multigate.op().toString().length());
		out += ")";
		return out;
	}
	@Override
	public String visit(ITEGate ite, Translate translate) {
		String out = "<";
		BooleanFormula i = ite.input(0);
		BooleanFormula t = ite.input(1);
		BooleanFormula e = ite.input(2);
		out += i.accept(this, translate)+"?";
		out += t.accept(this, translate)+":";
		out += e.accept(this, translate)+">";
		return out;
	}
	@Override
	public String visit(NotGate negation, Translate translate) {
		String out = "";
		out += negation.op();
		out += negation.input(0).accept(this, translate);
		return out;
	}
	@Override
	public String visit(BooleanVariable variable, Translate translate) {
		String out = "";
		if(variable.label==BooleanConstant.FALSE.label) out += "FALSE";
		else if(variable.label==BooleanConstant.TRUE.label) out += "TRUE";
		else out += translate.varToString(Math.abs(variable.label()), alloynames);
		return out;
	}
}
/*******************************************************************************
 * Linearizes the proof tree via unit propagation
 ******************************************************************************/
class UnitProper implements BooleanVisitor<BooleanFormula, Set<Integer>>  {
	final Set<Integer> units; 
	public UnitProper(Set<Integer> units) {
		this.units = units; 
	}
	@Override
	public BooleanFormula visit(MultiGate multigate, Set<Integer> propped) {
		BooleanAccumulator accum =  BooleanAccumulator.treeGate(multigate.op);
		Iterator<BooleanFormula> itr = multigate.iterator();
		while(itr.hasNext()) {
			BooleanFormula fml = itr.next();
			fml = fml.accept(this, propped);
			boolean extraOr = multigate.op()==Operator.Nary.OR && fml.label()==BooleanConstant.FALSE.label;
			boolean extraAnd = multigate.op()==Operator.Nary.AND && fml.label()==BooleanConstant.TRUE.label;
			if(!extraOr && !extraAnd) accum.add(fml);
		}
		if(accum.size()==0) {
			if(multigate.op()==Operator.Nary.AND) return new BooleanVariable(BooleanConstant.TRUE.label);
			if(multigate.op()==Operator.Nary.OR) return new BooleanVariable(BooleanConstant.FALSE.label);
		}
		if(accum.size()==1) {
			BooleanValue v = accum.iterator().next();
			try { return (BooleanFormula) v; }
			catch (Exception e) { return new BooleanVariable(v.label());}
		}
		return new NaryGate(accum, multigate.label(), multigate.hashCode());
	}
	@Override
	public BooleanFormula visit(ITEGate ite, Set<Integer> propped) {
		BooleanFormula i = ite.input(0);
		BooleanFormula t = ite.input(1);
		BooleanFormula e = ite.input(2);
		i = i.accept(this, propped);
		t = t.accept(this, propped);
		e = e.accept(this, propped);
		return new ITEGate(ite.label(), ite.hashCode(), i, t, e); 
	}
	@Override
	public BooleanFormula visit(NotGate negation, Set<Integer> propped) {
		BooleanFormula fml = negation.input(0).accept(this, propped);
		if(fml.label()==BooleanConstant.FALSE.label) return new BooleanVariable(BooleanConstant.TRUE.label);
		if(fml.label()==BooleanConstant.TRUE.label) return new BooleanVariable(BooleanConstant.FALSE.label);
		return new NotGate(fml);
	}
	@Override
	public BooleanFormula visit(BooleanVariable variable, Set<Integer> propped) {
		if (units.contains(-variable.label())) {
			propped.add(-variable.label());
			return new BooleanVariable(BooleanConstant.FALSE.label);
		}
		if (units.contains(variable.label())) {
			propped.add(variable.label());
			return new BooleanVariable(BooleanConstant.TRUE.label);
		}
		return variable;
	}
}
/*******************************************************************************
 * Checks if the given formula is a unit clause
 ******************************************************************************/
class UnitFinder implements BooleanVisitor<Integer, Boolean>  {
	@Override
	public Integer visit(MultiGate multigate, Boolean shouldNegate) {
		return 0;
	}
	@Override
	public Integer visit(ITEGate ite, Boolean shouldNegate) {
		return 0;
	}
	@Override
	public Integer visit(NotGate negation, Boolean shouldNegate) {
		return negation.input(0).accept(this, !shouldNegate);
	}
	@Override
	public Integer visit(BooleanVariable variable, Boolean shouldNegate) {
		if(variable.label==BooleanConstant.FALSE.label||variable.label==BooleanConstant.TRUE.label) return 0;
		return shouldNegate ? -variable.label : variable.label;
	}
}
/*******************************************************************************
 * Pushes all negations to variable level
 ******************************************************************************/
class NegationPusher implements BooleanVisitor<BooleanFormula, Boolean>  {
	@Override
	public BooleanFormula visit(MultiGate multigate, Boolean shouldNegate) {
		Operator.Nary opposite = multigate.op==Operator.Nary.OR ? Operator.Nary.AND : Operator.Nary.OR;
		Operator.Nary op = shouldNegate ? opposite : multigate.op;
		BooleanAccumulator accum =  BooleanAccumulator.treeGate(op);
		Iterator<BooleanFormula> itr = multigate.iterator();
		while(itr.hasNext()) {
			BooleanFormula fml = itr.next();
			fml = fml.accept(this, shouldNegate);
			accum.add(fml);
		}
		return new NaryGate(accum, multigate.label(), multigate.hashCode());
	}
	@Override
	public BooleanFormula visit(ITEGate ite, Boolean shouldNegate) {
		BooleanFormula i = ite.input(0);
		BooleanFormula t = ite.input(1);
		BooleanFormula e = ite.input(2);
		i = i.accept(this, shouldNegate);
		t = t.accept(this, shouldNegate);
		e = e.accept(this, shouldNegate);
		return new ITEGate(ite.label(), ite.hashCode(), i, t, e); 
	}
	@Override
	public BooleanFormula visit(NotGate negation, Boolean shouldNegate) {
		return negation.input(0).accept(this, !shouldNegate);
	}
	@Override
	public BooleanFormula visit(BooleanVariable variable, Boolean shouldNegate) {
		return shouldNegate ? new NotGate(variable) : variable;
	}
}

