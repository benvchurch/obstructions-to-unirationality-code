/*******************************************************************************
 * subgroups.m
 *
 * Purpose:
 *   Generate LaTeX diagrams of subgroup lattices using GraphViz and dot2tex.
 *   Creates publication-quality Hasse diagrams showing the subgroup structure
 *   of a finite group, with customizable labels (group names, genera, etc.)
 *
 * Main functions:
 *   - CreateSubgroupLatticeLaTeX(G : labels, output_prefix): Generate lattice diagram
 *
 * Output files (in diagrams/ subdirectory):
 *   - {output_prefix}_graphviz.txt: GraphViz source
 *   - {output_prefix}_raw.tex: Raw LaTeX from dot2tex
 *   - {output_prefix}.tex: Final LaTeX with proper labels
 *   - {output_prefix}.pdf: Compiled PDF
 *   - {output_prefix}_graphviz.pdf: Direct GraphViz PDF
 *
 * Dependencies:
 *   - External: dot (GraphViz), dot2tex, pdflatex
 *   - intermediate_extensions.m: GenusIntermediateExtension (for genus labels)
 *   - group_reps.m: FindBelyiCurve (in examples)
 *
 * Usage:
 *   output_file := CreateSubgroupLatticeLaTeX(G);
 *   // With custom labels (e.g., genera of intermediate curves):
 *   output_file := CreateSubgroupLatticeLaTeX(G : labels := genera,
 *                                             output_prefix := "lattice_genera");
 *
 * Note:
 *   Subscript numbers show the number of conjugates of each subgroup.
 ******************************************************************************/

// Single function that creates GraphViz code with placeholders, converts to LaTeX, then replaces labels
CreateSubgroupLatticeLaTeX := function(G : labels := [], output_prefix := "subgroup_lattice")
    // Create diagrams directory if it doesn't exist
    System("mkdir -p diagrams");
    
    lattice := SubgroupLattice(G);
    n := #lattice;

    // Create placeholder labels for GraphViz and proper LaTeX labels
    placeholder_labels := [];
    latex_labels := [];
    
    for i in [1..n] do
        H := lattice[i];
        // Create placeholder for GraphViz (simple text that GraphViz can handle)
        if i le 10 then
            placeholder := Sprintf("L0%oEND", i);
        else
            placeholder := Sprintf("L%oEND", i);
        end if;
        Append(~placeholder_labels, placeholder);
        
        // Create proper LaTeX label
        file := Open("diagrams/group_names.txt", "a");

        if #labels gt 0 and i le #labels then
            // Use provided labels with LaTeX format
            custom_label := labels[i];
            if H ne G and #H ne 1 then
                latex_label := Sprintf("${}_{\\textcolor{gray}{%o}} %o$", #Conjugates(G,H), custom_label);
            else
                latex_label := Sprintf("$%o$", custom_label);
            end if;
        else
            // Standard behavior with group identifiers
            try
                id := IdentifyGroup(H);
                group_label := Sprintf("%o_{%o}", id[1], id[2]);
            catch e
                group_label := Sprintf("%o", #H);
            end try;

            Puts(file, Sprintf("%o, %o\n", i, group_label));
            
            if H ne G and #H ne 1 then
                latex_label := Sprintf("${}_{\\textcolor{gray}{%o}} %o$", #Conjugates(G,H), group_label);
            else
                latex_label := Sprintf("$%o$", group_label);
            end if;
        end if;
        Append(~latex_labels, latex_label);
    end for;

    // Start building the DOT output string
    output := "digraph SubgroupLattice {\n";
    output := output cat "  rankdir=BT;\n"; // Draw from top (G) to bottom (trivial)
    output := output cat "  ranksep=1.3;\n";
    output := output cat "  node [shape=plaintext];\n";
    output := output cat "  edge [arrowhead=none];\n"; // Remove arrowheads

    // Add nodes with placeholder labels
    for i in [1..n] do
        output := output cat Sprintf("  %o [label=\"%o\"];\n", i, placeholder_labels[i]);
    end for;

    // For each pair (H < K), check if H is maximal in K
    for i in [1..n] do
        for j in [1..n] do
            if (lattice ! i) lt (lattice ! j) then
                // Check if there is no L with H < L < K
                is_cover := true;
                for l in [1..n] do
                    if ((lattice ! i) lt (lattice ! l)) and ((lattice ! l) lt (lattice ! j)) then
                        is_cover := false;
                        break;
                    end if;
                end for;
                if is_cover then
                    output := output cat Sprintf("  %o -> %o;\n", i, j);
                end if;
            end if;
        end for;
    end for;

    output := output cat "}";
    
    // Write GraphViz file in diagrams subfolder
    graphviz_file := Sprintf("diagrams/%o_graphviz.txt", output_prefix);
    file := Open(graphviz_file, "w");
    Puts(file, output);
    delete file;
    
    // Convert to LaTeX using dot2tex
    raw_tex_file := Sprintf("diagrams/%o_raw.tex", output_prefix);
    System(Sprintf("dot2tex -f tikz -o %o %o", raw_tex_file, graphviz_file));
    
    // Read the raw LaTeX file
    raw_tex := Read(raw_tex_file);
    
    // Replace placeholder labels with proper LaTeX labels
    final_tex := raw_tex;
    
    // Add centering and scaling to the tikzpicture environment
    pos := Position(final_tex, "\\begin{tikzpicture}[");
    if pos gt 0 then
        final_tex := Substring(final_tex, 1, pos-1) cat 
                    "\\\hspace{-3cm}\n\\begin{tikzpicture}[scale = 0.8," cat 
                    Substring(final_tex, pos + #"\\begin{tikzpicture}[", #final_tex);
    end if;
    
    for i in [1..n] do
        // Simple string replacement implementation
        pos := Position(final_tex, placeholder_labels[i]);
        while pos gt 0 do
            final_tex := Substring(final_tex, 1, pos-1) cat 
                        latex_labels[i] cat 
                        Substring(final_tex, pos + #placeholder_labels[i], #final_tex);
            pos := Position(final_tex, placeholder_labels[i]);
        end while;
    end for;
    
    // Write the final LaTeX file in diagrams subfolder
    final_tex_file := Sprintf("diagrams/%o.tex", output_prefix);
    file := Open(final_tex_file, "w");
    Puts(file, final_tex);
    delete file;
    
    // Also generate PDF directly from GraphViz for comparison
    pdf_file := Sprintf("diagrams/%o_graphviz.pdf", output_prefix);
    System(Sprintf("dot -Tpdf %o -o %o", graphviz_file, pdf_file));
    System(Sprintf("pdflatex -output-directory=diagrams %o", final_tex_file));

    return final_tex_file;
end function;

S := SymmetricGroup(14);
P := S!(1, 13, 2, 11, 4, 5, 8)(3, 10, 6, 14, 7, 9, 12);
Q := S!(1, 7, 3, 4)(2, 11, 13, 9, 6, 14, 10, 5);

G := sub<S | P,Q>;
// Example usage
output_file := CreateSubgroupLatticeLaTeX(G);
printf "Generated LaTeX file: %o\n", output_file;

U := P^2*Q;
T := P^3*Q;
seq := [U,T,(U*T)^(-1)];

subgroups := [Subgroups(G)[i]`subgroup : i in [1..#Subgroups(G)]];

genera := [];

for i in [1..#subgroups] do
    H := subgroups[i];
    Append(~genera, GenusIntermediateExtension(G, seq, H));
end for; 

output_file := CreateSubgroupLatticeLaTeX(G : labels := genera, output_prefix := "subgroup_lattice_genera");
printf "Generated LaTeX file: %o\n", output_file;

output_file := CreateSubgroupLatticeLaTeX(G : labels := [1..#subgroups], output_prefix := "subgroup_lattice_ordered");
printf "Generated LaTeX file: %o\n", output_file;




if false then

G := SmallGroup(1092,25);

// Example usage
output_file := CreateSubgroupLatticeLaTeX(G);
printf "Generated LaTeX file: %o\n", output_file;

import "intermediate_extensions.m" : GenusIntermediateExtension;
import "group_reps.m" : FindBelyiCurve;

seq := FindBelyiCurve(G, [2,3,5], 14);

subgroups := [Subgroups(G)[i]`subgroup : i in [1..#Subgroups(G)]];

genera := [];

for i in [1..#subgroups] do
    H := subgroups[i];
    Append(~genera, GenusIntermediateExtension(G, seq, H));
end for; 

output_file := CreateSubgroupLatticeLaTeX(G : labels := genera, output_prefix := "subgroup_lattice_genera");
printf "Generated LaTeX file: %o\n", output_file;

output_file := CreateSubgroupLatticeLaTeX(G : labels := [1..16], output_prefix := "subgroup_lattice_ordered");
printf "Generated LaTeX file: %o\n", output_file;

group_names := ["C_1", "C_2", "C_3", "C_7", "C_{13}", "C_2^2", "S_3", "C_6", "S_3", "D_{7}", "D_{13} ", "C_{13}\\rtimes C_3", "D_{6}", "A_4", "C_{13}\\rtimes C_6", "\\mathrm{PSL}_2(\\mathbb{F}_{13})"];
output_file := CreateSubgroupLatticeLaTeX(G : labels := group_names, output_prefix := "subgroup_lattice_group_names");
printf "Generated LaTeX file: %o\n", output_file; 

end if;