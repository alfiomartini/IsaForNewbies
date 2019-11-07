section\<open>  Uma Teoria para Listas Genéricas \<close>

theory list_no_text
imports nat_tutorial
begin

subsection\<open>Definições Básicas\<close>

datatype 'a  List  = Empty | cons 'a "'a List"

primrec cat::"'a List\<Rightarrow>'a List \<Rightarrow>'a List"
   where
     cat01: "cat Empty l = l"|
     cat02: "cat (cons h t) l= cons h (cat t l)"

subsection\<open> Verificação com scripts de comandos \<close>

theorem th_cat01as: "\<forall> l2 l3. cat l (cat l2 l3) = cat (cat l l2) l3"
   apply (induct l)
   apply (simp_all)
done

subsection\<open>Verificação com a linguagem Isar\<close>


theorem th_cat01isA: "\<forall> l2 l3. cat l (cat l2 l3) = cat (cat l l2) l3"
   proof (induct l)
     show "\<forall> l2 l3. cat Empty (cat l2 l3) = cat (cat Empty l2) l3" by simp
   next
     fix e0 and l0
     assume IH: "\<forall> l2 l3. cat l0 (cat l2 l3) = cat (cat l0 l2) l3"
     show "\<forall> l2 l3. cat (cons e0 l0) (cat l2 l3) = cat (cat (cons e0 l0) l2) l3" 
       by (simp add:IH)
   qed

 theorem th_cat01isB: "\<forall> l2 l3. cat l (cat l2 l3) = cat (cat l l2) l3"
   proof (induct l)
     show "\<forall> l2 l3. cat Empty (cat l2 l3) = cat (cat Empty l2) l3"
       proof (rule allI, rule allI)
         fix k and  m
         have "cat Empty (cat k m) = cat k m" by (simp only:cat01)
         also  have "cat k m = cat (cat Empty k) m" by (simp only:cat01)
         finally show "cat Empty (cat k m) = cat (cat Empty k) m" by this
       qed  
    next
      fix e0::'a and l0::"'a List"
      assume IH: "\<forall> l2 l3. cat l0 (cat l2 l3) = cat (cat l0 l2) l3"
      show "\<forall> l2 l3. cat (cons e0 l0) (cat l2 l3) = cat (cat (cons e0 l0) l2) l3"       
        proof (rule allI, rule allI)
          fix k and m
          have "cat (cons e0 l0) (cat k m) = cons e0 (cat l0  (cat k m))" 
             by (simp only:cat02)
          also have "cons e0 (cat l0 (cat k m)) = cons e0 (cat (cat l0 k) m)" 
              by (simp only:IH)
          also have "cons e0 (cat (cat l0 k) m) = cat (cons e0 (cat l0 k)) m" 
             by (simp only:cat02)
          also  have "cat (cons e0 (cat l0 k)) m = cat (cat (cons e0 l0) k) m" 
             by (simp only:cat02)
          finally  show "cat (cons e0 l0) (cat k m) =cat (cat (cons e0 l0) k) m" 
             by this
       qed  
   qed 

subsection\<open>Pit Stop\<close>

end