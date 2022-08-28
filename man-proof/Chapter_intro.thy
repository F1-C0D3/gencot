theory Chapter_intro
  imports Main
begin
chapter "Introduction"
text_raw\<open>\label{intro}\<close>

text \<open>
This manual describes how to prove functional properties for a Cogent program which resulted from translating a C program
using Gencot. It is not a general manual about working with Isabelle. It only uses a very restricted subset of Isabelle
features. It does not presume prior knowledge about Isabelle.

The Cogent compiler generates an Isabelle representation of the compiled program, the ``shallow embedding''. It mainly 
consists of definitions in the language of higher order logic for all functions defined in the Cogent program. The goal 
of the functional properties proofs described in this manual is to systematically develop more abstract definitions
which together form an abstract specification of the Cogent program and can be used to prove program properties which
are relevant for the use of the program, such as security properties.

The Cogent compiler also generates a C program and a proof that this program is a refinement of the shallow embedding,
i.e., it behaves in the same way. Thus, if combined with the refinement proof, the abstract specification can be 
applied to the C program and the functional properties proofs are also valid for the C program.
\<close>

end 
