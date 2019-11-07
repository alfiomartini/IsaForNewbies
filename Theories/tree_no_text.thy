section {* Uma Teoria para Árvores Genéricas *}
theory tree_no_text
imports list_tutorial
begin

subsection \<open> Definições Básicas\<close>

datatype 'a Tree = Leaf | Br  'a "'a Tree" "'a Tree"

 

primrec reflect::"'a Tree \<Rightarrow> 'a Tree"
   where
     ref01:"reflect Leaf = Leaf" |
     ref02:"reflect (Br label lt rt) = Br label (reflect rt) (reflect lt)"

 
subsection \<open>Verificação com scripts de comandos\<close>
 
theorem th_refl01as: "reflect (reflect t) = t" 
   apply (induct t)
   apply (auto)
done
 
subsection \<open>Verificação com a linguagem Isar \<close>

theorem th_refl01isA: "reflect (reflect t) = t"
  proof (induct t)
     show  "reflect (reflect Leaf) = Leaf" by simp
  next
     fix x0 and lt0::"'a Tree" and rt0::"'a Tree" 
     assume IH1: "reflect (reflect lt0) = lt0"
     assume IH2: "reflect (reflect rt0) = rt0"
     show "reflect (reflect (Br x0 lt0 rt0)) = Br x0 lt0 rt0" 
        by (simp add:IH1 IH2)
  qed 

theorem th_reflect01isB : "reflect (reflect t) = t"
  proof (induct t)
   show "reflect (reflect Leaf) = Leaf" 
     proof - 
       have "reflect (reflect Leaf)=reflect Leaf" by (simp only: ref01)
       also  have "reflect Leaf = Leaf" by (simp only:ref01)
       finally show "?thesis" by simp
     qed
  next
     fix x0 and  lt0::"'a Tree" and  rt0::"'a Tree" 
     assume IH1: "reflect (reflect lt0)=lt0" 
     assume  IH2:"reflect (reflect rt0)=rt0"
     show "reflect (reflect (Br x0 lt0 rt0)) = (Br x0 lt0 rt0)"
     proof -
       have "reflect (reflect (Br x0 lt0 rt0)) = 
        reflect (Br x0 (reflect rt0) (reflect lt0))" by (simp only:ref02)
       also have 
       "...= Br x0 (reflect (reflect lt0)) (reflect (reflect rt0))"
           by (simp  only:ref02)
       also have "... = Br x0 lt0 rt0" by (simp only:IH1 IH2)
       finally show  "reflect (reflect (Br x0 lt0 rt0)) = Br x0 lt0 rt0 " 
          by simp
     qed
  qed

section\<open> Comentários Finais \<close>
end