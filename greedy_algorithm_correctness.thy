theory greedy_algorithm_correctness
  imports Main Complex_Main
begin

definition "set_system E F = (finite E \<and> (\<forall> X \<in> F. X \<subseteq> E))"

definition accessible where "accessible E F \<longleftrightarrow> set_system E F \<and> ({} \<in> F) \<and> (\<forall>X. (X \<in> F - {{}}) \<longrightarrow>
(\<exists>x \<in> X.  X - {x} \<in> F))"
definition closed_under_union where "closed_under_union F \<longleftrightarrow> (\<forall>X Y. X \<in> F \<and> Y \<in> F \<longrightarrow> X \<union> Y \<in> F)"


definition maximal where "maximal P Z \<longleftrightarrow> (P Z \<and> (\<nexists> X. X \<supset> Z \<and> P X))"



lemma accessible_property:
  assumes "accessible E F"
  assumes "X \<subseteq> E" "X \<in> F"
  shows "\<exists>l. set l = X \<and>  (\<forall>i. i \<le> length l \<longrightarrow> set (take i l) \<in> F) \<and> distinct l"
  using assms
proof -
  have "set_system E F" using assms(1) unfolding accessible_def by simp
  then have "finite E" unfolding set_system_def by simp
  then have "finite X" using finite_subset assms(2) by auto
  obtain k where "card X = k" using \<open>finite X\<close> by simp 
  then show ?thesis using assms(3)
  proof (induct k arbitrary: X rule: less_induct)
    case (less a)
    then have "card X = a" by simp
    have "X \<in> F" by (simp add: less.prems(2))
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
      have "{} \<in> F" using assms(1) unfolding accessible_def by simp
      then have "\<forall>i. i \<le> length [] \<longrightarrow> set (take i l) \<in> F" using l_prop by simp
      then show ?thesis using \<open>l = []\<close> l_prop by simp
    next
      case False
      then have "X \<noteq> {}" using \<open>card X = a\<close> by auto
      then have "X \<in> F - {{}}" using \<open>X \<in> F\<close> by simp
      then obtain x where "x \<in> X" "X - {x} \<in> F" using \<open>X \<in> F\<close> assms(1) unfolding accessible_def by auto
      have "finite {x}" by simp
      then have factone: "finite (X - {x})" using \<open>finite X\<close> by simp
      have "(X - {x}) \<subset>  X" using \<open>x \<in> X\<close> by auto
      then have "card (X - {x}) < card (X)" by (meson \<open>finite X\<close> psubset_card_mono)
      then have "card (X - {x}) < a" using \<open>card X = a\<close> by simp
      then have "\<exists>l. set l = X - {x} \<and> (\<forall>i. i \<le> length l \<longrightarrow> set (take i l) \<in> F) \<and> distinct l" using \<open>X - {x} \<in> F\<close> 
        using less.hyps by blast 
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


locale greedoid =
  fixes E :: "'a set"
  fixes F :: "'a set set"
  assumes contains_empty_set: "{} \<in> F"
  assumes third_condition: "(X \<in> F) \<and> (Y \<in> F) \<and> (card X > card Y) \<Longrightarrow> \<exists>x \<in> X - Y.  Y \<union> {x} \<in> F"
  assumes ss_assum: "set_system E F"
  assumes acc_assum: "accessible E F"

definition strong_exchange_property where "strong_exchange_property E F \<longleftrightarrow> (\<forall>A B x. A \<in> F
\<and> B \<in> F \<and> A \<subseteq> B \<and> (maximal (\<lambda>B. B \<in> F) B) \<and> x \<in> E - B \<and> A \<union> {x} \<in> F \<longrightarrow> (\<exists>y. y \<in> B - A \<and> 
A \<union> {y} \<in> F \<and> (B - {y}) \<union> {x} \<in> F))"


locale greedy_algorithm = greedoid +
  fixes orcl::"'a set \<Rightarrow> bool"
  fixes es
  assumes orcl_correct: "\<And> X. X \<subseteq> E \<Longrightarrow> orcl X \<longleftrightarrow> X \<in> F"
  assumes set_assum: "set es = E \<and> distinct es" 


context greedy_algorithm
begin

  definition valid_modular_weight_func::"('a set \<Rightarrow> real) \<Rightarrow> bool" where  "valid_modular_weight_func c = (c ({}) = 0 \<and> (\<forall>X l. X \<subseteq> E \<and> X \<noteq> {} \<and> l = {c {e} | e. e \<in> X} \<and> c (X) = sum (\<lambda>x. real x) l))"

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
      then show ?case sorry
    qed
  qed

lemma valid_weight_prop: assumes "X \<subset> Y" "Y \<subseteq> E" "valid_modular_weight_func c" 
  shows "c Y > c X"
  sorry

lemma maximum_weight_prop: assumes "valid_modular_weight_func c" "maximum_weight_set c X"
  shows "maximal (\<lambda>X. X \<in> F) X"
  sorry

lemma greedy_algo_maximal: assumes "valid_modular_weight_func c" 
"\<exists>B. maximum_weight_set c B \<and> (greedy_algorithm_greedoid {} c) \<inter> B \<noteq> {}" 
shows "\<not> ((greedy_algorithm_greedoid {} c) \<subset> B)"
  sorry

lemma weight_func_empty: assumes "X \<in> F" "valid_modular_weight_func c" "X \<noteq> {}"
  shows "c X > c {}" using assms unfolding valid_modular_weight_func_def by auto

lemma greedy_algo_nonempty: assumes "valid_modular_weight_func c" "X \<in> F" "X \<noteq> {}"
  shows "greedy_algorithm_greedoid {} c \<noteq> {}"
  sorry


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
            have "maximal (\<lambda>Z. Z \<in> F) B" using maximum_weight_prop assum3 B_prop by simp
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
        assume assum1: "\<forall>c. valid_modular_weight_func c \<longrightarrow>
        maximum_weight_set c (greedy_algorithm_greedoid {} c)"
        show "strong_exchange_property E F"
        proof (rule ccontr)
          assume "\<not> strong_exchange_property E F"
          then have "\<forall>A B x.
       A \<in> F \<and>
       B \<in> F \<and> A \<subseteq> B \<and> maximal (\<lambda>B. B \<in> F) B \<and> x \<in> E - B \<and> A \<union> {x} \<in> F \<longrightarrow>
       (\<forall>y. y \<in> B - A \<and> A \<union> {y} \<in> F \<and> B - {y} \<union> {x} \<notin> F)" unfolding strong_exchange_property_def sorry
    
  


end

end