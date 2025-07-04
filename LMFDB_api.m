// Define a function to fetch the content of a URL using curl
function FetchURL(url)
    temp_filename := "temp_output.txt";
    // Build the curl command; note the use of quotes in case the URL contains special characters.
    curl_command := Sprintf("curl -L \"%o\" > %o", url, temp_filename);
    // Execute the system command. System returns an exit status (0 means success).
    status := System(curl_command);
    if status ne 0 then
        error "curl command failed with status:", status;
    end if;
    return temp_filename;
end function;

// Add this new function at the top
function RunWithTimeout(command, timeout_sec)
    status_filename := "timeout_status";
    // Use shell timeout command and write exit status to file
    full_command := Sprintf("echo \"%o\" | timeout %o  magma -b > /dev/null 2>&1; echo $? > %o", 
                          command, timeout_sec, status_filename);
    System(full_command);
    // Read exit status (124 means timeout occurred)
    status := StringToInteger(Read(status_filename));
    return status;
end function;

groupid := [16,3];

// Construct the API URL with proper URL encoding for square brackets
url := Sprintf("https://www.lmfdb.org/api/hgcwa_passports/?group=%%5B%o,%o%%5D&_format=json", 
             groupid[1], groupid[2]);

// Process JSON with jq to extract relevant fields and format as Magma code
json_filename := FetchURL(url);
magma_filename := "temp_processed.m";

// jq command to parse JSON and format for Magma
Curve := recformat<
    label: MonStgElt,
    genus: RngIntElt,
    gen_vectors: SeqEnum,
    jacobian_decomp: SeqEnum 
>;
jq_command := Sprintf("jq -r '\"[\" + ([(.data[] | \"rec<Curve|label := \\\"\" + .label + \"\\\", gen_vectors := \" + (.gen_vectors|tostring) + \", genus := \" + (.genus|tostring) + \", jacobian_decomp := \" + (.jacobian_decomp|tostring) + \">\") ] | join(\", \")) + \"]\"' %o > %o", 
                     json_filename, magma_filename);
System(jq_command);

// Load processed data into Magma
data_str := Read(magma_filename);
data := eval data_str;  // Convert string to Magma object

Sym := SymmetricGroup(groupid[1]);

load "invariants.m";

findData := function(G, seq1, seq2)
    Pi := Pi1([seq1, seq2], G);
    cmd := Sprintf("exit Order(%m);", Pi);
    completed := RunWithTimeout(cmd, 1);
    if completed ne 1 then
        return false;
    end if;
    rr13 := RR13Number([seq1, seq2], G);
    bruin := BruinNumber([seq1, seq2], G);
    diagonal := DiagonalFormNumber([seq1, seq2], G);
    
    return rr13 gt 0 or bruin gt 0 or diagonal gt 0;
end function;


// Modify the loop section to use timeout
for C1 in data do
    seq1 := [Sym ! v : v in (C1`gen_vectors)];
    G := sub<Sym | seq1>;
    if C1`genus lt 9 then
        continue;
    end if;
    for C2 in data do
        if C2`genus lt 9 then
            continue;
        end if;
        seq2 := [Sym ! v : v in (C2`gen_vectors)];
        print C1`genus,C2`genus;
        if findData(G, seq1, seq2) then
            print "FOUND";
            print C1`label,C1`label;
            rr13 := RR13Number([seq1, seq2], G);
            bruin := BruinNumber([seq1, seq2], G);
            diagonal := DiagonalFormNumber([seq1, seq2], G);
            print rr13,bruin,diagonal;
            print C1`jacobian_decomp, C2`jacobian_decomp;
        end if;
    end for;
end for;

        