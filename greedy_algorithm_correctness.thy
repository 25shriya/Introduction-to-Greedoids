theory greedy_algorithm_correctness
  imports Main Complex_Main
begin

definition "set_system E F = (finite E \<and> (\<forall> X \<in> F. X \<subseteq> E))"

definition accessible where "accessible E F \<longleftrightarrow> set_system E F \<and> ({} \<in> F) \<and> (\<forall>X. (X \<in> F - {{}}) \<longrightarrow>
(\<exists>x \<in> X.  X - {x} \<in> F))"
definition closed_under_union where "closed_under_union F \<longleftrightarrow> (\<forall>X Y. X \<in> F \<and> Y \<in> F \<longrightarrow> X \<union> Y \<in> F)"


definition maximal where "maximal P Z \<longleftrightarrow> (P Z \<and> (\<nexists> X. X \<supset> Z \<and> P X))"

lemma set_take_union_nth:
  assumes "i < length l"
  shows "set (take i l) \<union> {nth l i} = set (take (i + 1) l)"
proof -
  have "take (i + 1) l = take i l @ [nth l i]"
    using  take_Suc_conv_app_nth assms by simp
  then have "set (take (i + 1) l) = set (take i l @ [nth l i])"
    by simp
  also have "... = set (take i l) \<union> set [nth l i]"
    by simp
  finally show ?thesis
    by simp
qed


lemma accessible_property: assumes "set_system E F" "{} \<in> F"
  shows "accessible E F \<longleftrightarrow> (\<forall>X. X \<in> F \<longrightarrow> (\<exists>l. set l = X \<and>  (\<forall>i. i \<le> length l \<longrightarrow> set (take i l) \<in> F) \<and> distinct l))"
proof 
  show "accessible E F \<Longrightarrow>
    \<forall>X. X \<in> F \<longrightarrow> (\<exists>l. set l = X \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l)"
  proof -
    assume "accessible E F"
    show "\<forall>X. X \<in> F \<longrightarrow> (\<exists>l. set l = X \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l)"
    proof
      fix X
      show "X \<in> F \<longrightarrow> (\<exists>l. set l = X \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l)"
      proof
        assume "X \<in> F"
  have "set_system E F" using assms(1) unfolding accessible_def by simp
  then have "finite E" unfolding set_system_def by simp
  have "X \<subseteq> E" using assms \<open>X \<in> F\<close> unfolding set_system_def by auto
  then have "finite X" using finite_subset \<open>finite E\<close> by auto
  obtain k where "card X = k" using \<open>finite X\<close> by simp 
  then show "(\<exists>l. set l = X \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l)" using assms \<open>X \<in> F\<close> \<open>X \<subseteq> E\<close>
  proof (induct k arbitrary: X rule: less_induct)
    case (less a)
    then have "card X = a" by simp
    have "X \<in> F" using \<open>X \<in> F\<close> by auto
    then have "X \<subseteq> E" using \<open>set_system E F\<close> unfolding set_system_def by simp
    then have "finite X" using \<open>finite E\<close> finite_subset by auto
    then show ?case
    proof (cases "a = 0")
      case True
      then have "card X = 0" using \<open>card X = a\<close> by simp
      have "\<not>(infinite X)" using \<open>finite X\<close> by simp        
      then have "X = {}" using \<open>card X = 0\<close> by simp
      then obtain l where l_prop: "set l = X" "distinct l" using finite_distinct_list by auto
      then have "l = []" using l_prop \<open>X = {}\<close> by simp
      have "{} \<in> F" using assms \<open>accessible E F\<close> unfolding accessible_def by simp
      then have "\<forall>i. i \<le> length [] \<longrightarrow> set (take i l) \<in> F" using l_prop by simp
      then show ?thesis using \<open>l = []\<close> l_prop by simp
    next
      case False
      then have "X \<noteq> {}" using \<open>card X = a\<close> by auto
      then have "X \<in> F - {{}}" using \<open>X \<in> F\<close> by simp
      then obtain x where "x \<in> X" "X - {x} \<in> F" using \<open>X \<in> F\<close> \<open>accessible E F\<close> unfolding accessible_def by auto
      have "finite {x}" by simp
      then have factone: "finite (X - {x})" using \<open>finite X\<close> by simp
      have "(X - {x}) \<subset>  X" using \<open>x \<in> X\<close> by auto
      then have "card (X - {x}) < card (X)" by (meson \<open>finite X\<close> psubset_card_mono)
      then have "card (X - {x}) < a" using \<open>card X = a\<close> by simp 
      have "X - {x} \<subseteq> E" using \<open>X - {x} \<subset> X\<close> \<open>X \<subseteq> E\<close> by simp
      then have "\<exists>l. set l = X - {x} \<and> (\<forall>i. i \<le> length l \<longrightarrow> set (take i l) \<in> F) \<and> distinct l" using \<open>X - {x} \<in> F\<close> 
        using less.hyps \<open>X - {x} \<in> F\<close> \<open>card (X - {x}) < a\<close> assms by simp
      then obtain l where l_prop: "set l = X - {x} \<and> (\<forall>i. i \<le> length l \<longrightarrow> set (take i l) \<in> F) \<and> distinct l" by auto
      let ?l' = "l @ [x]"
      have conc1: "distinct ?l'" using l_prop by simp
      have l_prop2: "set l = X - {x}" using l_prop by simp
      have "(X - {x}) \<union> {x} = X" using \<open>x \<in> X\<close> by auto
      then have conc2: "(set ?l') = X" using l_prop2 by simp
      have prop2: "(\<forall>i. i < length ?l' \<longrightarrow> set (take i ?l') \<in> F)" using l_prop by simp
      have "set (take (length ?l') ?l') \<in> F" using \<open>set ?l' = X\<close> \<open>X \<in> F\<close> by simp
      then have "(\<forall>i. i \<le> length ?l' \<longrightarrow> set (take i ?l') \<in> F)" using prop2
        using antisym_conv2 by blast
       then show ?thesis using conc1 conc2 by fast
     qed
   qed
 qed
qed
qed
  show "\<forall>X. X \<in> F \<longrightarrow>
        (\<exists>l. set l = X \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l) \<Longrightarrow>
    accessible E F"
    unfolding accessible_def
  proof 
    show "\<forall>X. X \<in> F \<longrightarrow>
        (\<exists>l. set l = X \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l) \<Longrightarrow>
    set_system E F" using assms by simp
    show "\<forall>X. X \<in> F \<longrightarrow>
        (\<exists>l. set l = X \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l) \<Longrightarrow>
    {} \<in> F \<and> (\<forall>X. X \<in> F - {{}} \<longrightarrow> (\<exists>x\<in>X. X - {x} \<in> F))"
    proof 
      show "\<forall>X. X \<in> F \<longrightarrow>
        (\<exists>l. set l = X \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l) \<Longrightarrow>
    {} \<in> F" using assms by simp
      show "\<forall>X. X \<in> F \<longrightarrow>
        (\<exists>l. set l = X \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l) \<Longrightarrow>
    \<forall>X. X \<in> F - {{}} \<longrightarrow> (\<exists>x\<in>X. X - {x} \<in> F)"
      proof -
        assume assum1: "\<forall>X. X \<in> F \<longrightarrow>
        (\<exists>l. set l = X \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l)"
        show "\<forall>X. X \<in> F - {{}} \<longrightarrow> (\<exists>x\<in>X. X - {x} \<in> F)"
        proof
          fix X
          show "X \<in> F - {{}} \<longrightarrow> (\<exists>x\<in>X. X - {x} \<in> F)"
          proof
            assume "X \<in> F - {{}}"
            then have "X \<noteq> {}" by simp
            then have "(\<exists>l. set l = X \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l)" using assum1 \<open>X \<in> F - {{}}\<close> by simp
            then obtain l where l_prop: "set l = X \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l" by auto
            then have "l \<noteq> []" using \<open>X \<noteq> {}\<close> by auto
            then obtain x where "(nth l (length l - 1)) = x" by simp
            then have "set (take (length l) l) \<in> F" using l_prop by auto
            have "length l > 0" using \<open>l \<noteq> []\<close> by simp
            then have "length l - 1 < length l" by simp
            then have factone: "(set (take (length l - 1) l)) \<union> {nth l (length l - 1)} = set (take (length l) l)" 
              using set_take_union_nth by fastforce
            have facttwo: "nth l (length l - 1) \<notin> set (take (length l - 1) l)" 
            proof
              assume assum2: "l ! (length l - 1) \<in> set (take (length l - 1) l)"
              then have "(take (length l - 1)  l) \<noteq> []" by auto
              then have assum3: "List.member (take (length l - 1) l) (nth l (length l - 1))" using in_set_member \<open>l \<noteq> []\<close>
                assum2 by fast
              have "l = (take (length l - 1) l) @ [nth l (length l - 1)]" using \<open>l \<noteq> []\<close> 
                by (metis Suc_diff_1 \<open>0 < length l\<close> \<open>length l - 1 < length l\<close> order_refl take_Suc_conv_app_nth take_all_iff)
              then have "\<not> (distinct l)"
                using assum2 distinct_take not_distinct_conv_prefix by blast
              then show False using l_prop by simp
            qed
            have "set (take (length l - 1) l) \<in> F" using l_prop by simp
            then have  "((set (take (length l) l)) - {nth l (length l - 1)}) \<in> F" using factone facttwo 
              by (metis Diff_insert_absorb Un_empty_right Un_insert_right)
            then have "X - {x} \<in> F" using l_prop \<open>nth l (length l - 1) = x\<close> by simp
            have "x \<in> X" using l_prop \<open>nth l (length l - 1) = x\<close> in_set_member \<open>l \<noteq> []\<close> by auto
            then show "\<exists>x\<in>X. X - {x} \<in> F" using \<open>X - {x} \<in> F\<close> by auto
          qed
        qed
      qed
    qed
  qed
qed

    

lemma first_element_set:
  assumes "l \<noteq> []"
  shows "{nth l 0} = set (take 1 l)"
proof -
  from assms obtain a l' where l_def: "l = a # l'"
    by (cases l) auto
  then have "nth l 0 = a" by simp
  moreover have "take 1 l = [a]" using l_def by simp
  ultimately show "{nth l 0} = set (take 1 l)" by simp
qed




locale greedoid =
  fixes E :: "'a set"
  fixes F :: "'a set set"
  assumes contains_empty_set: "{} \<in> F"
  assumes third_condition: "(X \<in> F) \<and> (Y \<in> F) \<and> (card X > card Y) \<Longrightarrow> \<exists>x \<in> X - Y.  Y \<union> {x} \<in> F"
  assumes ss_assum: "set_system E F"

context greedoid
begin

lemma greedoid_accessible: assumes "greedoid E F"
  shows "accessible E F" unfolding accessible_def
 proof
   show "set_system E F" using ss_assum assms by auto 
   show "{} \<in> F \<and> (\<forall>X. X \<in> F - {{}} \<longrightarrow> (\<exists>x\<in>X. X - {x} \<in> F))"
   proof
     show "{} \<in> F" using contains_empty_set by simp
     show "\<forall>X. X \<in> F - {{}} \<longrightarrow> (\<exists>x\<in>X. X - {x} \<in> F)"
     proof
       fix X
       show "X \<in> F - {{}} \<longrightarrow> (\<exists>x\<in>X. X - {x} \<in> F)"
       proof
         assume "X \<in> F - {{}}"
         then have "X \<subseteq> E" using ss_assum unfolding set_system_def by simp
         have "X \<noteq> {}" using \<open>X \<in> F - {{}}\<close> by simp
         have "finite E" using ss_assum unfolding set_system_def by simp
         then have "finite X" using \<open>X \<subseteq> E\<close> finite_subset by auto    
         have facttwo: "\<forall>i. i \<ge> 0 \<and> i < card X \<longrightarrow> (\<exists>x \<in> X. (\<exists>Y  Z. Y \<in> F \<and> Z \<in> F \<and> Y \<subseteq> X \<and> Z \<subset> Y \<and> card Y = i + 1 \<and> card Z = i \<and> (Y - Z) = {x} ))"
         proof 
           fix i
           show "i \<ge> 0 \<and> i < card X \<longrightarrow> (\<exists>x \<in> X. (\<exists>Y  Z. Y \<in> F \<and> Z \<in> F \<and> Y \<subseteq> X \<and> Z \<subset> Y \<and> card Y = i + 1 \<and> card Z = i \<and> (Y - Z) ={x} ))"
           proof
             assume assum2: "0 \<le> i \<and> i < card X"
             then show "(\<exists>x \<in> X. (\<exists>Y  Z. Y \<in> F \<and> Z \<in> F \<and> Y \<subseteq> X \<and> Z \<subset> Y \<and> card Y = i + 1 \<and> card Z = i \<and> (Y - Z) = {x} ))" using \<open>X \<in> F - {{}}\<close>
                 \<open>finite X\<close>
             proof (induct i arbitrary: X rule: less_induct)
               case (less i)
               then show ?case
               proof (cases "i = 0")
                 case True
                 have 1: "card {} = 0" by simp
                 have "X \<noteq> {}" using \<open>X \<in> F - {{}}\<close> by simp
                 then have "card X > card {}" using \<open>finite X\<close> by auto
                 then have "\<exists>x. x \<in> X - {} \<and> {} \<union> {x} \<in> F" using contains_empty_set \<open>X \<in> F - {{}}\<close> third_condition by blast
                 then obtain x where x_prop: "x \<in> X - {} \<and> {} \<union> {x} \<in> F" by auto
                 then have 2: "{x} \<in> F" by simp
                 have 3: "{x} \<subseteq> X" using x_prop by simp
                 have 4: "{} \<subset> {x}" by auto
                 have 5: "card {x} = 0 + 1" by simp
                 have "card ({x} - {}) = 1" by simp
                 then show ?thesis using 1 2 3 4 5 contains_empty_set x_prop True by blast
               next 
                 case False
                 then have "i > 0 \<and> i < card X" using \<open>i \<ge> 0 \<and> i < card X\<close> by simp
                 then have factone: "i - 1 < i" by simp
                 then have "i - 1 \<ge> 0 \<and> (i - 1) < card X" using \<open>i > 0 \<and> i < card X\<close> by auto
                 then have "(\<exists>x \<in> X. (\<exists>Y  Z. Y \<in> F \<and> Z \<in> F \<and> Y \<subseteq> X \<and> Z \<subset> Y \<and> card Y = (i - 1) + 1  \<and> card Z = i - 1 \<and> (Y - Z) = {x} ))"
                   using \<open>finite X\<close> \<open>X \<in> F - {{}}\<close> less.hyps factone by blast
                 then have "(\<exists>x \<in> X. (\<exists>Y  Z. Y \<in> F \<and> Z \<in> F \<and> Y \<subseteq> X \<and> Z \<subset> Y \<and> card Y = i \<and> card Z = i - 1 \<and> (Y - Z) = {x} ))"
                   using factone by simp
                 then obtain x Y Z where x_Y_Z_prop: "x \<in> X \<and> Y \<in> F \<and> Z \<in> F \<and> Y \<subseteq> X \<and> Z \<subset> Y \<and> card Y = i \<and> card Z = i - 1 \<and> (Y - Z) = {x}" by auto
                 then have "card Y < card X" using \<open>i > 0 \<and> i < card X\<close> by simp
                 have 2: "card Y = i" using x_Y_Z_prop by simp
                 have "Y \<in> F" using x_Y_Z_prop by simp
                 then have "\<exists>x. x \<in> X - Y \<and> Y \<union> {x} \<in> F" using third_condition \<open>X \<in> F - {{}}\<close> \<open>card Y < card X\<close> by auto
                 then obtain y where y_prop: "y \<in> X - Y \<and> Y \<union> {y} \<in> F" by auto
                 then have "y \<notin> Y" by simp
                 then have "card (Y \<union> {y}) = card Y + card {y}" using \<open>card Y = i\<close> 
                   by (metis Nat.add_0_right \<open>0 < i \<and> i < card X\<close> add_Suc_right card_1_singleton_iff card_gt_0_iff card_insert_disjoint insert_is_Un sup_commute)
                 then have 1: "card (Y \<union> {y}) = i + 1" using \<open>card Y = i\<close> by simp
                 have 3: "Y \<union> {y} \<subseteq> X" using y_prop x_Y_Z_prop by simp
                 have 4: "Y \<subset> Y \<union> {y}" using \<open>y \<notin> Y\<close> by auto
                 then have "((Y \<union> {y}) - Y) = {y}" by auto
                 then show ?thesis using 1 2 3 4 y_prop x_Y_Z_prop \<open>X \<in> F - {{}}\<close> \<open>finite X\<close>
                   by (metis Diff_iff)
               qed
             qed
           qed
         qed
         have "card X \<noteq> 0" using \<open>X \<noteq> {}\<close> \<open>finite X\<close> by simp
         then have "card X - 1 < card X" by simp
         have "card X - 1 \<ge> 0" by simp
         then have "(\<exists>x \<in> X. (\<exists>Y  Z. Y \<in> F \<and> Z \<in> F \<and> Y \<subseteq> X \<and> Z \<subset> Y \<and> card Y = (card X - 1) + 1 \<and> card Z = card X - 1 \<and> (Y - Z) = {x} ))"
           using \<open>card X - 1 < card X\<close> facttwo by blast
         then obtain x Y Z where x_Y_Z_prop: "x \<in> X \<and> Y \<in> F \<and> Z \<in> F \<and> Y \<subseteq> X \<and> Z \<subset> Y \<and> card Y = (card X - 1) + 1 \<and> card Z = card X - 1 \<and> (Y - Z) = {x}"
           by auto
         then have "card Y = card X" using \<open>card X - 1 < card X\<close> by simp
         have "Y \<subseteq> X" using x_Y_Z_prop by simp
         then have "Y = X" using x_Y_Z_prop \<open>finite X\<close> \<open>card Y = card X\<close> 
           using card_subset_eq by blast
         have "Y - {x} = Z" using x_Y_Z_prop by auto
         then have "X - {x} = Z" using \<open>Y = X\<close> by simp
         also have "... \<in> F" using x_Y_Z_prop by simp
         finally have "X - {x} \<in> F" by simp
         then show "\<exists>x\<in>X. X - {x} \<in> F" using x_Y_Z_prop by auto
       qed
     qed
   qed
 qed
                
              
          
       
         


end

definition strong_exchange_property where "strong_exchange_property E F \<longleftrightarrow> (\<forall>A B x. A \<in> F
\<and> B \<in> F \<and> A \<subseteq> B \<and> (maximal (\<lambda>B. B \<in> F) B) \<and> x \<in> E - B \<and> A \<union> {x} \<in> F \<longrightarrow> (\<exists>y \<in> B - A. 
A \<union> {y} \<in> F \<and> (B - {y}) \<union> {x} \<in> F))"


locale greedy_algorithm = greedoid +
  fixes orcl::"'a set \<Rightarrow> bool"
  fixes es
  assumes orcl_correct: "\<And> X. X \<subseteq> E \<Longrightarrow> orcl X \<longleftrightarrow> X \<in> F"
  assumes set_assum: "set es = E \<and> distinct es" 


context greedy_algorithm
begin

  definition valid_modular_weight_func::"('a set \<Rightarrow> real) \<Rightarrow> bool" where  "valid_modular_weight_func c = (c ({}) = 0 \<and> (\<forall>X l. X \<subseteq> E \<and> X \<noteq> {} \<and> l = {c {e} | e. e \<in> X} \<and> c (X) = sum (\<lambda>x. x) l))"

  definition "maximum_weight_set c X = (X \<in> F \<and> (\<forall> Y \<in> F. c X \<ge> c Y))"

  definition "find_best_candidate c F' = foldr (\<lambda> e acc. if e \<in> F' \<or> \<not> orcl (insert e F') then acc
                                                      else (case acc of None \<Rightarrow> Some e |
                                                               Some d \<Rightarrow> (if c {e} > c {d} then Some e
                                                                          else Some d))) es None"

(*Next two lemmas taken as facts: the best candidate for F' lies in es (list of E), and does not lie in F'.*)
lemma find_best_candidate_in_es: assumes "F' \<subseteq> E" "find_best_candidate c F' = Some x"
  shows "List.member es x"
  sorry
lemma find_best_candidate_notin_F': assumes "F' \<subseteq> E" "find_best_candidate c F' = Some x"
  shows "x \<notin> F'"
proof -
  have "foldr (\<lambda> e acc. if e \<in> F' \<or> \<not> orcl (insert e F') then acc
                                                      else (case acc of None \<Rightarrow> Some e |
                                                               Some d \<Rightarrow> (if c {e} > c {d} then Some e
                                                                          else Some d))) es None = Some x" using assms(2) unfolding find_best_candidate_def by auto
  then obtain acc where "foldr (\<lambda> e acc. if e \<in> F' \<or> \<not> orcl (insert e F') then acc
                                                      else (case acc of None \<Rightarrow> Some e |
                                                               Some d \<Rightarrow> (if c {e} > c {d} then Some e
                                                                          else Some d))) es acc = Some x" by simp
  show ?thesis
    sorry
qed

function (domintros) greedy_algorithm_greedoid::"'a set \<Rightarrow> ('a set \<Rightarrow> real) \<Rightarrow> 'a set" where "greedy_algorithm_greedoid F' c = (if (E = {} \<or> \<not>(F' \<subseteq> E)) then undefined 
else  (case  (find_best_candidate c F') of Some e => greedy_algorithm_greedoid(F' \<union> {the (find_best_candidate c F')}) c | None => F'))"
proof -
  show "\<And>P x. (\<And>F' c. x = (F', c) \<Longrightarrow> P) \<Longrightarrow> P" by auto
  show "\<And>F' c F'a ca.
       (F', c) = (F'a, ca) \<Longrightarrow>
       (if E = {} \<or> \<not> F' \<subseteq> E then undefined
        else case find_best_candidate c F' of None \<Rightarrow> F'
             | Some e \<Rightarrow>
                 greedy_algorithm_greedoid_sumC
                  (F' \<union> {the (find_best_candidate c F')}, c)) =
       (if E = {} \<or> \<not> F'a \<subseteq> E then undefined
        else case find_best_candidate ca F'a of None \<Rightarrow> F'a
             | Some e \<Rightarrow>
                 greedy_algorithm_greedoid_sumC
                  (F'a \<union> {the (find_best_candidate ca F'a)}, ca))"
  proof -
    fix F' c F'a ca
    show "(F', c) = (F'a, ca) \<Longrightarrow>
       (if E = {} \<or> \<not> F' \<subseteq> E then undefined
        else case find_best_candidate c F' of None \<Rightarrow> F'
             | Some e \<Rightarrow>
                 greedy_algorithm_greedoid_sumC
                  (F' \<union> {the (find_best_candidate c F')}, c)) =
       (if E = {} \<or> \<not> F'a \<subseteq> E then undefined
        else case find_best_candidate ca F'a of None \<Rightarrow> F'a
             | Some e \<Rightarrow>
                 greedy_algorithm_greedoid_sumC
                  (F'a \<union> {the (find_best_candidate ca F'a)}, ca))"
    proof -
      assume assum1: "(F', c) = (F'a, ca)"
      then have 1: "F' = F'a"by simp
      have "c = ca" using assum1 by simp
      then show ?thesis using 1 by auto
    qed
  qed
qed

lemma greedy_algo_term: shows "All greedy_algorithm_greedoid_dom"
proof (relation "measure (\<lambda>(F', c). card (E - F'))")
  show " wf (measure (\<lambda>(F', c). card (E - F')))" by (rule wf_measure)
  show "\<And>F' c x2.
       \<not> (E = {} \<or> \<not> F' \<subseteq> E) \<Longrightarrow>
       find_best_candidate c F' = Some x2 \<Longrightarrow>
       ((F' \<union> {the (find_best_candidate c F')}, c), F', c)
       \<in> measure (\<lambda>(F', c). card (E - F'))"
  proof -
    fix F' c x
    show "\<not> (E = {} \<or> \<not> F' \<subseteq> E) \<Longrightarrow>
       find_best_candidate c F' = Some x \<Longrightarrow>
       ((F' \<union> {the (find_best_candidate c F')}, c), F', c)
       \<in> measure (\<lambda>(F', c). card (E - F'))"
    proof - 
      assume assum1: "\<not> (E = {} \<or> \<not> F' \<subseteq> E)"
      show "find_best_candidate c F' = Some x \<Longrightarrow>
    ((F' \<union> {the (find_best_candidate c F')}, c), F', c)
    \<in> measure (\<lambda>(F', c). card (E - F'))"
      proof -
        assume assum2: "find_best_candidate c F' = Some x"
        then have "List.member es x" using find_best_candidate_in_es assum1 by auto
        then have "length es > 0" using assum1 set_assum by auto
        then have "x \<in> set es" using in_set_member \<open>List.member es x\<close> assum1 by fast
        then have "x \<in> E" using set_assum by simp
        have "x \<notin> F'" using assum1 assum2 find_best_candidate_notin_F' by auto
        then have "x \<in> E - F'" using \<open>x \<in> E\<close> assum1 by simp
        then have "F' \<subset> F' \<union> {the (find_best_candidate c F')}" using \<open>x \<notin> F'\<close> assum2 by auto
        then have "E - (F' \<union> {the (find_best_candidate c F')}) \<subset> E - F'" 
          by (metis Diff_insert Diff_insert_absorb Un_empty_right Un_insert_right \<open>x \<in> E - F'\<close> assum2 mk_disjoint_insert option.sel psubsetI subset_insertI)
      have "finite E" using ss_assum unfolding set_system_def by simp
      then have "finite F'" using finite_subset assum1 by auto
      then have "finite (E - F')" using \<open>finite E\<close> by blast
      then have "card (E - (F' \<union> {the (find_best_candidate c F')})) < card (E - F')" 
        using \<open>E - (F' \<union> {the (find_best_candidate c F')}) \<subset> E - F'\<close> psubset_card_mono by auto
      then show ?thesis by auto
  qed
qed
qed
qed

lemma greedy_algo_best_candidate: assumes "valid_modular_weight_func c"
  shows "find_best_candidate c (greedy_algorithm_greedoid {} c) = None"
  using greedy_algo_term sorry

lemma max_weight_exists: assumes "greedoid E F" "valid_modular_weight_func c"
  shows "\<exists>F'. maximum_weight_set c F'"
proof -
  have "set_system E F" using ss_assum by simp
  then have "finite E" unfolding set_system_def by simp
  then have "finite F" using \<open>set_system E F\<close> unfolding set_system_def
    by (meson Sup_le_iff finite_UnionD finite_subset)
  let ?A = "{c F' | F'. F' \<in> F}"
  have "finite ?A" using \<open>finite F\<close> by simp
  have "F \<noteq> {}" using contains_empty_set by auto
  then have "?A \<noteq> {}" by simp
  then obtain x where "x = Max ?A" using \<open>finite ?A\<close> by simp
  then have "x \<in> ?A" using Max_in \<open>finite ?A\<close> \<open>?A \<noteq> {}\<close> by auto
  then obtain F' where F'_prop: "F' \<in> F \<and> c F' = x" by auto
  then have max_fact: "\<forall>a. a \<in> ?A \<longrightarrow> x \<ge> a" 
    by (simp add: \<open>finite ?A\<close> \<open>x = Max ?A\<close>)
  have "maximum_weight_set c F'" unfolding maximum_weight_set_def
  proof (rule ccontr)
    assume "\<not> (F' \<in> F \<and> (\<forall>Y\<in>F. c Y \<le> c F'))"
    then have contr: "F' \<notin> F \<or> \<not> (\<forall>Y\<in>F. c Y \<le> c F')" by simp
    have "F' \<in> F" using F'_prop by simp
    then have "\<not> (\<forall>Y\<in>F. c Y \<le> c F')" using contr by simp
    then have "\<exists>X. X \<in> F \<and> c X > c F'" by auto
    then obtain X where "X \<in> F \<and> c F' < c X" by auto
    then have "c X \<in> ?A" by auto
    then have "c X > x" using \<open>F' \<in> F \<and> c F' = x\<close> \<open>X \<in> F \<and> c F' < c X\<close> by simp
    then show "False" using max_fact \<open>c X \<in> ?A\<close> by auto
  qed
  then show ?thesis by auto
qed

lemma greedy_algo_in_F: 
  assumes "valid_modular_weight_func c"
  shows "(greedy_algorithm_greedoid {} c) \<in> F"
proof -
  define measure_func where "measure_func = (\<lambda>(F', c). card (E - F'))"
  have wf_measure: "wf (measure measure_func)"
    using greedy_algo_term by simp
  show ?thesis
  proof (induction rule: wf_induct[of "measure measure_func"])
    case 1
    show ?case
    proof (cases "E = {} \<or> \<not> F' \<subseteq> E")
      case True
      then show ?thesis by simp
    next
      case False
      then obtain e where e_prop: "find_best_candidate c F' = Some e \<or> find_best_candidate c F' = None"
        by auto
      have factone: "E \<noteq> {} \<and> F' \<subseteq> E" using False by simp
      then have "F' \<subseteq> E" by simp
      show ?thesis
      proof (cases "find_best_candidate c F' = Some e")
        case True
        then have "e \<in> E" 
          using find_best_candidate_in_es find_best_candidate_notin_F'
          by (metis False in_set_member set_assum)
        then have "e \<notin> F'" 
          using find_best_candidate_notin_F' \<open>F' \<subseteq> E\<close> True by auto
        have "F' \<union> {e} \<subseteq> E"
          using `e \<in> E` `F' \<subseteq> E` by auto
        then show ?thesis by simp
      next
        case False
        then have "find_best_candidate c F' = None" using e_prop by simp
        then have "greedy_algorithm_greedoid F' c = F'" 
          by (simp add: factone greedy_algo_term greedy_algorithm_greedoid.psimps)
        then show ?thesis by simp
      qed
    qed
    next 
      case (2 x)
      fix x
      show "\<forall>y. (y, x) \<in> measure measure_func \<longrightarrow>
             greedy_algorithm_greedoid {} c \<in> F \<Longrightarrow>
         greedy_algorithm_greedoid {} c \<in> F"
      proof -
        assume assum1: "\<forall>y. (y, x) \<in> measure measure_func \<longrightarrow>
             greedy_algorithm_greedoid {} c \<in> F"
        then show ?case 
        proof (cases "\<forall>y. (y, x) \<in> measure measure_func")
          case True
          then show ?thesis using assum1 by simp
        next
          case False
          then have "\<exists>y. (y, x) \<notin> measure measure_func" by simp
          then obtain y where "(y, x) \<notin> measure measure_func" by auto
          then show ?thesis using assum1 by auto
        qed
  qed
qed
qed

lemma valid_weight_prop: assumes "X \<subset> Y" "valid_modular_weight_func c" "Y \<noteq> {}" "X \<in> F"
"Y \<in> F"
  shows "c Y > c X"
proof (cases "X = {}")
  case True
  then show ?thesis using assms unfolding valid_modular_weight_func_def by auto
next
  case False
  then have "c X > 0" using assms unfolding valid_modular_weight_func_def by auto
  let ?l1 = "{c {e} | e. e \<in> X}"
  let ?l2 = "{c {e} | e. e \<in> Y}"
  let ?l3 = "{c {e} | e. e \<in> Y - X}"
  have X_val: "c X = sum (\<lambda>x. x) ?l1" using assms unfolding valid_modular_weight_func_def by auto
  have Y_val: "c Y = sum (\<lambda>x. x) ?l2" using assms unfolding valid_modular_weight_func_def by auto
  have "Y - X \<noteq> {}" using assms False by simp
  then have "?l3 \<noteq> {}" using assms unfolding valid_modular_weight_func_def by auto
  have "finite E" using ss_assum unfolding set_system_def by simp
  have "Y \<subseteq> E" using assms ss_assum unfolding set_system_def by simp
  then have "finite Y" using finite_subset \<open>finite E\<close> by auto
  then have "finite (Y - X)" using finite_subset by auto
  then have "finite ?l3" using assms unfolding valid_modular_weight_func_def by auto
  have "?l2 = ?l1 \<union> ?l3" using assms unfolding valid_modular_weight_func_def by auto
  then have "sum (\<lambda>x. x) ?l2 = sum (\<lambda>x. x) (?l1 \<union> ?l3)" by simp
  also have "... = sum (\<lambda>x. x) ?l1 + sum (\<lambda>x. x) ?l3" using assms unfolding valid_modular_weight_func_def by auto
  finally have prop_one: "sum (\<lambda>x. x) ?l2 = sum (\<lambda>x. x) ?l1 + sum (\<lambda>x. x) ?l3" by simp
  have "sum (\<lambda>x. x) ?l3 > 0" using \<open>finite ?l3\<close> \<open>?l3 \<noteq> {}\<close>  assms unfolding valid_modular_weight_func_def by auto
  then have "sum (\<lambda>x. x) ?l2 > sum (\<lambda>x. x) ?l1" using assms unfolding valid_modular_weight_func_def by auto
  then show ?thesis using X_val Y_val by simp
qed

lemma maximum_weight_prop: assumes "valid_modular_weight_func c" "maximum_weight_set c X" "X \<noteq> {}"
  shows "maximal (\<lambda>X. X \<in> F) X"
  unfolding maximal_def
proof
  show "X \<in> F" using assms unfolding maximum_weight_set_def by simp
  show "\<nexists>Xa. X \<subset> Xa \<and> Xa \<in> F"
  proof
    assume "\<exists>Xa. X \<subset> Xa \<and> Xa \<in> F"
    then obtain Y where Y_prop: "X \<subset> Y \<and> Y \<in> F" by auto
    then have "Y \<noteq> {}" using assms(3) by auto
    then have "c Y > c X" using valid_weight_prop assms(1) assms(3) Y_prop \<open>X \<in> F\<close> by auto
    then show False using assms(2) Y_prop unfolding maximum_weight_set_def by auto
  qed
qed



lemma greedy_algo_maximal: assumes "valid_modular_weight_func c" 
"maximum_weight_set c B " " (greedy_algorithm_greedoid {} c) \<inter> B \<noteq> {}" 
shows "\<not> ((greedy_algorithm_greedoid {} c) \<subset> B)"
proof
  assume assum1: "greedy_algorithm_greedoid {} c \<subset> B"
  let ?A = "greedy_algorithm_greedoid {} c"
  have "B \<in> F" using assms unfolding maximum_weight_set_def by auto
  have "?A \<in> F" using assms(1) greedy_algo_in_F by simp
  have "finite E" using ss_assum unfolding set_system_def by simp
  have "B \<subseteq> E" using \<open>B \<in> F\<close> using ss_assum unfolding set_system_def by simp
  then have "finite B" using \<open>finite E\<close> finite_subset by auto
  have "B \<noteq> {}" using assms by auto
  then have "card ?A < card B" using \<open>finite B\<close> assum1 psubset_card_mono by auto
  then have "\<exists>y \<in> B - ?A. ?A \<union> {y} \<in> F" using third_condition \<open>?A \<in> F\<close> \<open>B \<in> F\<close> by simp
  then obtain y where y_prop: "y \<in> B - ?A" "?A \<union> {y} \<in> F" by auto
    let ?Y = "{y | y. y \<in> B - ?A \<and> ?A \<union> {y} \<in> F}"
    have "y \<in> ?Y" using y_prop by simp
    have "finite ?Y" using \<open>finite B\<close> by simp
    have "?Y \<noteq> {}" using \<open>y \<in> ?Y\<close> by auto
    let ?l1 = "{c {e} | e. e \<in> ?Y}"
    have "finite ?l1" using assms(1) unfolding valid_modular_weight_func_def by auto
    have "?l1 \<noteq> {}" using assms(1) unfolding valid_modular_weight_func_def by auto
    then have "Max ?l1 \<in> ?l1" using Max_in \<open>finite ?l1\<close> by auto
    then have "\<forall>x. x\<in> ?l1 \<longrightarrow> x \<le> Max ?l1" using \<open>finite ?l1\<close> by auto
    then obtain e where "e \<in> ?Y" "c {e} = Max ?l1" using \<open>finite ?l1\<close> \<open>finite ?Y\<close> \<open>Max ?l1 \<in> ?l1\<close>
      by auto
    have "find_best_candidate c ?A = Some e" unfolding find_best_candidate_def
      sorry
    then show False using greedy_algo_best_candidate assms by auto
  qed


lemma weight_func_empty: assumes "X \<in> F" "valid_modular_weight_func c" "X \<noteq> {}"
  shows "c X > c {}" using assms unfolding valid_modular_weight_func_def by auto

lemma greedy_algo_nonempty: assumes "valid_modular_weight_func c" "X \<in> F" "X \<noteq> {}"
  shows "greedy_algorithm_greedoid {} c \<noteq> {}"
proof 
  assume "greedy_algorithm_greedoid {} c = {}"

  then have "find_best_candidate c {} = None" by auto


lemma set_union_ineq: assumes "valid_modular_weight_func c" "e \<in> E" "f \<in> E" "c {e} \<ge> c {f}" "Z \<subseteq> E"
"{e} \<union> Z \<in> F" "{f} \<union> Z \<in> F"
shows "c ({e} \<union> Z) \<ge> c ({f} \<union> Z)"
  sorry



lemma exists_maximal_weight_set: assumes "\<not> maximum_weight_set c (greedy_algorithm_greedoid {} c)" 
"valid_modular_weight_func c" "greedoid E F"
shows "\<exists>l. set l = (greedy_algorithm_greedoid {} c) \<and>  (\<forall>i. i \<le> length l \<longrightarrow> (set (take i l) \<in> F \<and> (\<forall>y. y \<in> E \<and> set (take (i - 1) l) \<union> {y} \<in> F \<longrightarrow> c {nth l i} \<ge> c {y}))) \<and> 
distinct l \<and> (\<exists>X. maximum_weight_set c X \<and> (\<exists>i. i < length l \<and> set (take i l) \<subseteq> X \<and> (\<nexists>j. j > i \<and> j \<le> length l \<and> (set (take j l)) \<subseteq> X) \<and> 
(\<forall>Y. maximum_weight_set c Y \<longrightarrow> (\<exists>k. set (take k l) \<subseteq> Y \<and> k < length l \<and> (\<nexists>j. j > k \<and> j \<le> length l \<and> (set (take j l)) \<subseteq> Y) \<and> k \<le> i))))" 
proof -
  let ?A = "greedy_algorithm_greedoid {} c"
  have "?A \<in> F" using greedy_algo_in_F assms(2) by simp
  then have "?A \<subseteq> E" using ss_assum unfolding set_system_def by simp
  then have "\<exists>l. set l = (greedy_algorithm_greedoid {} c) \<and>  (\<forall>i. i \<le> length l \<longrightarrow> set (take i l) \<in> F) \<and> distinct l" using 
accessible_property acc_assum \<open>?A \<in> F\<close> by blast
  then obtain l where l_prop: "set l = (greedy_algorithm_greedoid {} c) \<and>  (\<forall>i. i \<le> length l \<longrightarrow> set (take i l) \<in> F) \<and> distinct l" by auto
  have "\<exists>X. maximum_weight_set c X" using max_weight_exists assms(2-3) by simp
  then obtain B where "maximum_weight_set c B" by auto
  have fact1: "(\<exists>i. i < length l \<and> set (take i l) \<subseteq> B \<and> (\<nexists>j. j > i \<and> j \<le> length l \<and> (set (take j l)) \<subseteq> B) \<and> 
(\<forall>Y. maximum_weight_set c Y \<longrightarrow> (\<exists>k. set (take k l) \<subseteq> Y \<and> k < length l \<and> (\<nexists>j. j > k \<and> j \<le> length l \<and> (set (take j l)) \<subseteq> Y) \<and> k \<le> i)))"
  proof (cases "\<forall>i. i \<le> length l \<and> B \<inter> set (take i l) = {}")
    case True
    then show ?thesis sorry
  next
    case False   
    then show ?thesis sorry
  qed
  have fact2: "\<forall>i. i \<le> length l \<longrightarrow> (\<forall>y. y \<in> E \<and> set (take (i - 1) l) \<union> {y} \<in> F \<longrightarrow> c {nth l i} \<ge> c {y})" sorry
  then show ?thesis using l_prop \<open>maximum_weight_set c B\<close> fact1 
      by (smt (verit))
qed

  lemma greedy_algorithm_correctness:
    assumes assum1: "greedoid E F"
    shows "(\<forall>c. valid_modular_weight_func c \<longrightarrow> maximum_weight_set c (greedy_algorithm_greedoid {} c)) \<longleftrightarrow>
  strong_exchange_property E F"
  proof
    show "strong_exchange_property E F \<Longrightarrow>
    \<forall>c. valid_modular_weight_func c \<longrightarrow>
        maximum_weight_set c (greedy_algorithm_greedoid {} c)"
    proof
      fix c
      show "strong_exchange_property E F \<Longrightarrow>
         valid_modular_weight_func c \<longrightarrow>
         maximum_weight_set c (greedy_algorithm_greedoid {} c)"
      proof
        assume assum2: "strong_exchange_property E F"
        show "valid_modular_weight_func c \<Longrightarrow>
    maximum_weight_set c (greedy_algorithm_greedoid {} c)"
        proof -
          assume assum3: "valid_modular_weight_func c"
          show "maximum_weight_set c (greedy_algorithm_greedoid {} c)"
          proof (rule ccontr)
            assume assum4: "\<not> maximum_weight_set c (greedy_algorithm_greedoid {} c)"
            let ?A = "greedy_algorithm_greedoid {} c"
            have "accessible E F" using acc_assum by auto 
            have "?A \<in> F" using greedy_algo_in_F using assum3 by simp
            then have "\<exists>l. set l = (greedy_algorithm_greedoid {} c) \<and>  (\<forall>i. i \<le> length l \<longrightarrow> (set (take i l) \<in> F \<and> (\<forall>y. y \<in> E \<and> set (take (i - 1) l) \<union> {y} \<in> F \<longrightarrow> c {nth l i} \<ge> c {y}))) \<and> 
distinct l \<and> (\<exists>X. maximum_weight_set c X \<and> (\<exists>i. i < length l \<and> set (take i l) \<subseteq> X \<and> (\<nexists>j. j > i \<and> j \<le> length l \<and> (set (take j l)) \<subseteq> X) \<and> 
(\<forall>Y. maximum_weight_set c Y \<longrightarrow> (\<exists>k. set (take k l) \<subseteq> Y \<and> k < length l \<and> (\<nexists>j. j > k \<and> j \<le> length l \<and> (set (take j l)) \<subseteq> Y) \<and> k \<le> i))))"
              using assum3  exists_maximal_weight_set assum4 assms by auto
            then obtain l where l_prop: "set l = (greedy_algorithm_greedoid {} c) \<and>  (\<forall>i. i \<le> length l \<longrightarrow> (set (take i l) \<in> F \<and> (\<forall>y. y \<in> E \<and> set (take (i - 1) l) \<union> {y} \<in> F \<longrightarrow> c {nth l i} \<ge> c {y}))) \<and> 
distinct l \<and> (\<exists>X. maximum_weight_set c X \<and> (\<exists>i. i < length l \<and> set (take i l) \<subseteq> X \<and> (\<nexists>j. j > i \<and> j \<le> length l \<and> (set (take j l)) \<subseteq> X) \<and> 
(\<forall>Y. maximum_weight_set c Y \<longrightarrow> (\<exists>k. set (take k l) \<subseteq> Y \<and> k < length l \<and> (\<nexists>j. j > k \<and> j \<le> length l \<and> (set (take j l)) \<subseteq> Y) \<and> k \<le> i))))"
              by auto
            then obtain B where B_prop: "maximum_weight_set c B \<and> (\<exists>i. i < length l \<and> set (take i l) \<subseteq> B \<and> (\<nexists>j. j > i \<and> j \<le> length l \<and> (set (take j l)) \<subseteq> B) \<and> 
(\<forall>Y. maximum_weight_set c Y \<longrightarrow> (\<exists>k. set (take k l) \<subseteq> Y \<and> k < length l \<and> (\<nexists>j. j > k \<and> j \<le> length l \<and> (set (take j l)) \<subseteq> Y) \<and> k \<le> i)))" by auto
            then obtain k where k_prop: "k < length l \<and> set (take k l) \<subseteq> B \<and> (\<nexists>j. j > k \<and> j \<le> length l \<and>  (set (take j l)) \<subseteq> B) \<and> (\<forall>Y. maximum_weight_set c Y \<longrightarrow> (\<exists>i. set (take i l) \<subseteq> Y \<and> i < length l \<and> ((\<nexists>j. j > i \<and> j \<le> length l \<and> (set (take j l)) \<subseteq> Y))  \<and> i \<le> k))" by auto
            have "B \<in> F" using B_prop unfolding maximum_weight_set_def by simp
            then have "B \<subseteq> E" using ss_assum unfolding set_system_def by simp
            have "B \<noteq> ?A" using assum4 B_prop by auto
            have "?A \<subseteq> E" using \<open>?A \<in> F\<close> ss_assum unfolding set_system_def by auto
            show False
            proof (cases "B = {}")
              case True
              then have "?A \<noteq> {}" using \<open>B \<noteq> ?A\<close> by simp
              then have "c ?A > c B" using assum3 weight_func_empty \<open>?A \<in> F\<close> True by simp
              then show ?thesis using B_prop unfolding maximum_weight_set_def using \<open>?A \<in> F\<close> by auto
            next
              case False
              then have "?A \<noteq> {}" using assum3 \<open>B \<in> F\<close> greedy_algo_nonempty by simp
              have "l \<noteq> []" using l_prop False by auto
              show ?thesis
              proof -
                have "set l = ?A" using l_prop by simp
                have "l \<noteq> []" using \<open>?A \<noteq> {}\<close> l_prop by auto
                have "(nth l k) \<notin> B"
                proof
                  assume assum5: "(nth l k) \<in> B"
                  have set_prop1: "(set (take k l)) \<union> {nth l (k)} = set (take (k+1) l)" using set_take_union_nth k_prop by auto
                  have "set (take k l) \<union> {nth l k} \<subseteq> B" using k_prop assum5 by simp
                  then have set_prop2: "set (take (k+1) l) \<subseteq> B" using set_prop1 by blast
                  have "k + 1 > k" by simp
                  have "k + 1 \<noteq> length l"
                  proof
                    assume "k + 1 = length l"
                    then have "set (take (length l) l) \<subseteq> B" using set_prop2 by simp
                    show False
                    proof (cases "set (take (length l) l) = B")
                      case True
                      then have "?A = B" using \<open>set l = ?A\<close> by simp
                      then show ?thesis using B_prop assum4 by simp
                    next
                      case False
                      then have "set (take (length l) l) \<subset> B" using set_prop2 \<open>k + 1 = length l\<close> by fastforce
                      then have "?A \<subset> B" using \<open>set l = ?A\<close> by simp
                      then have "?A \<inter> B \<noteq> {}" using \<open>?A \<noteq> {}\<close> \<open>B \<noteq> {}\<close> by auto 
                      then show ?thesis using greedy_algo_maximal assum3 B_prop \<open>?A \<subset> B\<close> by auto
                    qed
                  qed
                  then have "k + 1 < length l" using k_prop by simp
                  then show False using set_prop2 k_prop by simp
                qed
                let ?x = "nth l k"
                have "?x \<in> ?A" using \<open>l \<noteq> []\<close> \<open>set l = ?A\<close> 
                  by (metis k_prop nth_mem)
                have "?x \<in> E" using \<open>(nth l k) \<in> ?A\<close> \<open>?A \<subseteq> E\<close> by auto
                then have "?x \<in> E - B" using \<open>?x \<notin> B\<close> by simp
                have set_prop1: "(set (take k l)) \<union> {?x} = set (take (k+1) l)" using set_take_union_nth k_prop by auto
                also have "... \<in> F" using k_prop l_prop by simp
                finally have "(set (take k l)) \<union> {?x} \<in> F" by simp 
                have "maximal (\<lambda>Z. Z \<in> F) B" using maximum_weight_prop assum3 \<open>B \<noteq> {}\<close> B_prop by simp
                have "set (take k l) \<in> F" using l_prop k_prop by simp
                then have "(\<exists>y. y \<in> B - (set (take k l)) \<and> set (take k l) \<union> {y} \<in> F \<and> (B - {y}) \<union> {?x} \<in> F)" using assum2 
                  unfolding strong_exchange_property_def using  \<open>B \<in> F\<close> \<open>?x \<in> E - B\<close>
                    \<open>maximal (\<lambda>Z. Z \<in> F) B\<close> k_prop \<open>set (take k l) \<union> {?x} \<in> F\<close> by blast
                then obtain y where y_prop: "y \<in> B - set (take k l) \<and> (set (take k l)) \<union> {y} \<in> F \<and> (B - {y}) \<union> {?x} \<in> F" by auto
                then have "y \<in> E" using \<open>B \<subseteq> E\<close> by auto
                have "y \<in> B" using y_prop by simp
                have "B - {y} \<subseteq> E" using \<open>B \<subseteq> E\<close> by auto
                have "(B - {y}) \<union> {?x} \<in> F" using y_prop by simp
                have l_prop2: "(\<forall>i \<le> length l. (\<forall>y \<in> E. set (take (i - 1) l) \<union> {y} \<in> F \<longrightarrow> c {nth l i} \<ge> c {y}))"
                  using l_prop by simp
                have "k + 1 - 1 = k" by simp
                have "set (take k l) \<union> {y} \<in> F"  using y_prop by simp
                then have "set (take ((k + 1) - 1) l) \<union> {y} \<in> F" using \<open>(k + 1) - 1 = k\<close> by fastforce
                then have "{y} \<union> set (take ((k + 1) - 1) l) \<in> F" by simp
                then have "k + 1 \<le> length l" using k_prop by simp
                then have " c {?x} \<ge> c {y}" using \<open>y \<in> E\<close> l_prop2 \<open>set (take ((k + 1) - 1) l) \<union> {y} \<in> F\<close> sorry
(*No proof for above line! It is quite direct*)
                have "{?x} \<union> (B - {y}) \<in> F" using y_prop by simp
                have "(B - {y}) \<union> {y} = B" using \<open>y \<in> B\<close> by auto
                then have "(B - {y}) \<union> {y} \<in> F" using \<open>B \<in> F\<close> by simp 
                then have "c ({?x} \<union> (B - {y})) \<ge> c ({y} \<union> (B - {y}))" using
                      set_union_ineq assum3 \<open>c {?x} \<ge> c {y}\<close> \<open>y \<in> E\<close> \<open>?x \<in> E\<close> \<open>(B - {y}) \<subseteq> E\<close> \<open>{?x} \<union> (B - {y}) \<in> F\<close>  
                  by (metis sup_commute)
                then have set_prop: "c ({?x} \<union> (B - {y})) \<ge> c B" using \<open>y \<in> B\<close> 
                  by (simp add: insert_absorb)
                have "maximum_weight_set c ({?x} \<union> (B - {y}))"
                proof (cases "c ({?x} \<union> (B - {y})) = c B")
                  case True
                  then show ?thesis using B_prop \<open>(B - {y}) \<union> {?x} \<in> F\<close> unfolding maximum_weight_set_def by simp
                next
                  case False
                  then have "c ({?x} \<union> (B - {y})) > c B" using set_prop by simp
                  show ?thesis 
                  proof (rule ccontr)
                    assume "\<not> maximum_weight_set c ({?x} \<union> (B - {y}))"
                    then have "c ({?x} \<union> (B - {y})) \<le> c B" using B_prop \<open>(B - {y}) \<union> {?x} \<in> F\<close> unfolding maximum_weight_set_def by auto
                    then show False using \<open>c ({?x} \<union> (B - {y})) > c B\<close> by simp
                  qed
                qed
                let ?Y = "{?x} \<union> (B - {y})"
                have "(\<exists>i. set (take i l) \<subseteq> ?Y \<and> i < length l \<and> ((\<nexists>j. j > i \<and> j \<le> length l \<and> (set (take j l)) \<subseteq> ?Y))  \<and> i \<le> k)"
                  using k_prop \<open>maximum_weight_set c ?Y\<close> by simp
                then obtain i where i_prop: "set (take i l) \<subseteq> ?Y \<and> i < length l \<and> ((\<nexists>j. j > i \<and> j \<le> length l \<and> (set (take j l)) \<subseteq> ?Y))  \<and> i \<le> k" by auto
                have "set (take k l) \<subseteq> B - {y}" using k_prop y_prop by auto
                then have "set (take k l) \<subseteq> {?x} \<union> (B - {y})" by auto
                  have set_prop3: "set (take (k+1) l) \<subseteq> ?Y"
                  proof
                    fix x
                    show "x \<in> set (take (k + 1) l) \<Longrightarrow> x \<in> {l ! k} \<union> (B - {y})"
                    proof -
                      assume x_assum: "x \<in> set (take (k + 1) l)"
                      show "x \<in> {l ! k} \<union> (B - {y})"
                      proof (cases "x \<in> set (take k l)")
                        case True
                        then show ?thesis using \<open>set (take k l) \<subseteq> {?x} \<union> (B - {y})\<close> by auto
                      next
                        case False
                        then have "x \<in> {?x}" using \<open>(set (take k l)) \<union> {?x} = set (take (k + 1) l)\<close> using x_assum by auto
                        then show ?thesis by simp
                      qed
                    qed
                  qed
                  have "i < k + 1" using i_prop by simp
                  then show False using set_prop3 i_prop \<open>k + 1 \<le> length l\<close> by simp
                qed
              qed
            qed
          qed
        qed
      qed
      show "\<forall>c. valid_modular_weight_func c \<longrightarrow>
        maximum_weight_set c (greedy_algorithm_greedoid {} c) \<Longrightarrow>
    strong_exchange_property E F "
      proof -
        assume assum6: "\<forall>c. valid_modular_weight_func c \<longrightarrow>
        maximum_weight_set c (greedy_algorithm_greedoid {} c)"
        show "strong_exchange_property E F"
        proof (rule ccontr)
          assume "\<not> strong_exchange_property E F"
          then have "\<exists>A B x. A \<in> F \<and> maximal (\<lambda>B. B \<in> F) B \<and> A \<subseteq> B \<and> x \<in> E - B \<and> A \<union> {x} \<in> F \<and> 
        (\<forall>y \<in> B - A. \<not> (A \<union> {y} \<in> F \<and> (B - {y}) \<union> {x} \<in> F))" unfolding strong_exchange_property_def by auto
          then obtain A B x where A_B_x_prop: "A \<in> F \<and> maximal (\<lambda>B. B \<in> F) B \<and> A \<subseteq> B \<and> x \<in> E - B \<and> A \<union> {x} \<in> F \<and> 
        (\<forall>y \<in> B - A. \<not> (A \<union> {y} \<in> F \<and> (B - {y}) \<union> {x} \<in> F))" by auto
          show False
          proof (cases "B = {}")
            case True
            then have "A = {}" using A_B_x_prop by simp
            have "maximal (\<lambda>B. B \<in> F) B" using A_B_x_prop by simp
            then have B_prop: "B \<in> F \<and> (\<nexists>X. X \<in> F \<and> B \<subset> X)" unfolding maximal_def by auto
            have "{x} \<in> F" using \<open>A = {}\<close> A_B_x_prop by simp
            have "B \<subset> {x}" using True by auto
            then show ?thesis using B_prop \<open>{x} \<in> F\<close> by simp
          next
            case False
            then show ?thesis
            proof (cases "B = A")
              case True
              then have "maximal (\<lambda>B. B \<in> F) A" using A_B_x_prop by simp
              then have A_prop: "A \<in> F \<and> (\<nexists>X. X \<in> F \<and> A \<subset> X)" unfolding maximal_def by auto
              have "x \<notin> A" using A_B_x_prop by auto
              then have "A \<subset> A \<union> {x}" by auto
              then show ?thesis using A_prop A_B_x_prop by simp
            next
              case False
              then have "A \<subset> B" using A_B_x_prop by auto
              have B_prop: "B \<in> F \<and> (\<nexists>X. X \<in> F \<and> B \<subset> X)" using A_B_x_prop unfolding maximal_def by auto
              then have "B \<subseteq> E" using ss_assum unfolding set_system_def by simp
              have "finite E" using ss_assum unfolding set_system_def by simp
              then have "finite B" using \<open>B \<subseteq> E\<close> finite_subset by auto
              then have "card A < card B" using \<open>A \<subset> B\<close> psubset_card_mono by auto
              then have "\<exists>y \<in> B - A. A \<union> {y} \<in> F"using B_prop A_B_x_prop third_condition by auto
              then obtain y where y_prop: "A \<union> {y} \<in> F" "y \<in> B - A" by auto
              then have "(B - {y})\<union> {x} \<notin> F" using A_B_x_prop by simp
              let ?Y = "{y | y. y \<in> B - A \<and> A \<union> {y} \<in> F }"
              have "finite ?Y" using \<open>finite B\<close> by simp
              have "?Y \<noteq> {}" using y_prop by auto
              
              then show ?thesis sorry
            qed
          qed
        qed
      qed
    qed


end

end