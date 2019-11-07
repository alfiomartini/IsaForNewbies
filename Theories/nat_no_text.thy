theory nat_no_text 
imports Main  
        "HOL-Library.LaTeXsugar"
begin

 
subsection\<open> Definições Básicas\<close>
 

datatype Nat = Z | suc Nat

 


primrec add::"Nat \<Rightarrow> Nat \<Rightarrow> Nat" 
  where
    add01:  "add x Z = x" |
    add02:  "add x (suc y) = suc (add x y)"

 
subsection\<open> Verificação com scripts de comandos\<close>

 

theorem th_add01as : "\<forall> x y. add (add x y) z = add x (add y z)"
 
  apply (induct z)
  apply (simp) \<comment> \<open>resolve o caso base\<close>
  apply (simp) \<comment> \<open>resolve o caso indutivo\<close>
     
done 

subsection\<open> Verificação com  a linguagem Isar \<close>

theorem th_add01isA : "\<forall> x y.  add (add x y) z = add x (add y z)"
  proof(induct z)
  \<comment> \<open>prova do caso base\<close>
    show "\<forall> x y. add (add x y) Z = add x (add y Z)" by simp
  next 
    fix x0::Nat \<comment> \<open>elemento arbitrário, mas fixo\<close>
    assume IH: "\<forall> x y. add (add x y) x0 = add x (add y x0)"
    show "\<forall> x y. add (add x y) (suc x0) = add x (add y (suc x0))" by (simp add:IH)
  qed


theorem th_add01isB:"\<forall> x y.  add (add x y) z = add x (add y z)"
  proof (induct z)
    show "\<forall> x y. add (add x y) Z = add x (add y Z)"
      proof (rule allI, rule allI)
        fix x0::Nat and y0::Nat
        have "add (add x0 y0) Z = add x0 y0" by (simp only:add01)
        also have "...  = add x0 (add y0 Z)" by (simp only:add01)
        finally show "add (add x0 y0) Z = add x0 (add y0 Z)" by simp
      qed
  next \<comment> \<open>pega o próximo subojetivo, isto é, o passo de indução\<close>
    fix z0::Nat
    assume IH: "\<forall> x y. add (add x y) z0 = add x (add y z0)"
    show "\<forall> x y. add (add x y) (suc z0) = add x (add y (suc z0))"
      proof (rule allI, rule allI)
        fix x0::Nat and y0::Nat
        have "add (add x0 y0) (suc z0) = suc (add (add x0 y0) z0)" 
         by (simp only:add02) 
        also have "...  = suc (add x0 (add y0 z0))" by (simp only:IH)
        also have "... = add x0 (suc (add y0 z0))" by (simp only:add02)
        also have "... = add x0 (add y0 (suc z0))" by (simp only:add02)
        finally 
        show "add (add x0 y0) (suc z0) = add x0 (add y0 (suc z0))" by simp
     qed
  qed

primrec mult::"Nat \<Rightarrow> Nat \<Rightarrow> Nat" where
   mult01: "mult x Z = Z" |
   mult02: "mult x (suc y) = add x (mult x y)"

 
subsection\<open> Pit Stop\<close>
end
