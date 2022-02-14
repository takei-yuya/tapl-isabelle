theory Term31
imports Main
begin

chapter \<open>3.5. Evaluation\<close>

section \<open>definition\<close>

datatype t 
  = true
  | false
  | Cond t t t ("If _ Then _ Else _" [95,95,95] 90)

inductive eval :: "t \<Rightarrow> t \<Rightarrow> bool" ("_ \<mapsto> _" [50,50] 40)
  where
    E_IfTrue: "If true Then t2 Else t3 \<mapsto> t2"
  | E_IfFalse: "If false Then t2 Else t3 \<mapsto> t3"
  | E_If:  "t1 \<mapsto> t1' \<Longrightarrow> If t1 Then t2 Else t3 \<mapsto> If t1' Then t2 Else t3"

definition is_value :: "t \<Rightarrow> bool"
  where "is_value t \<longleftrightarrow> (t = true \<or> t = false)"

lemma true_is_value[intro]: "is_value true" using is_value_def by simp
lemma false_is_value[intro]: "is_value false" using is_value_def by simp
lemma if_isnot_value: "is_value (If t1 Then t2 Else t3) \<Longrightarrow> False" using is_value_def by simp

lemma ex_353:
  assumes s: "s = If true Then false Else false"
  assumes t: "t = If s Then true Else true"
  assumes u: "u = If false Then true Else true"
  shows "If t Then false Else false \<mapsto> If u Then false Else false"
  apply (simp add: s t u)
  apply (rule E_If)
  apply (rule E_If)
  apply (rule E_IfTrue)
  done

lemma true_cannot_eval: "\<not>(\<exists>t. true \<mapsto> t)"
  using eval.cases by blast

lemma false_cannot_eval: "\<not>(\<exists>t. false \<mapsto> t)"
  using eval.cases by blast

lemma eval_IfTrue_eq_then: "If true Then t2 Else t3 \<mapsto> t2' \<Longrightarrow> t2' = t2"
  using eval.cases true_cannot_eval by auto

lemma eval_IfFalse_eq_else: "If false Then t2 Else t3 \<mapsto> t3' \<Longrightarrow> t3' = t3"
  using eval.cases false_cannot_eval by auto

section \<open>3.5.4 deterministic of eval\<close>

(* 3.5.4 *)
theorem eval_deterministic: "\<lbrakk> t \<mapsto> t'; t \<mapsto> t'' \<rbrakk> \<Longrightarrow> t' = t''"
proof(induct t arbitrary: t' t'')
  case true thus ?case using true_cannot_eval by blast 
next
  case false thus ?case using false_cannot_eval by blast 
next
  case Cond
  fix t1 t2 t3 t t''
  assume t1_induct: "\<And>t' t''. t1 \<mapsto> t' \<Longrightarrow> t1 \<mapsto> t'' \<Longrightarrow> t' = t''"
  assume et': "If t1 Then t2 Else t3 \<mapsto> t'"
  assume et'': "If t1 Then t2 Else t3 \<mapsto> t''"
  show "t' = t''"
  proof (cases t1)
    case true
    have "t' = t2" using true eval_IfTrue_eq_then et' by simp
    also have "t'' = t2" using true eval_IfTrue_eq_then et'' by simp
    finally show "t' = t''" by simp
  next
    case false
    have "t' = t3" using false eval_IfFalse_eq_else et' by simp
    also have "t'' = t3" using false eval_IfFalse_eq_else et'' by simp
    finally show "t' = t''" by simp
  next
    case Cond
    obtain t1' where t1t1': "t1 \<mapsto> t1'" and t'if: "t' = (If t1' Then t2 Else t3)"
      using Cond et' eval.cases by blast 
    obtain t1'' where t1t1'': "t1 \<mapsto> t1''" and t''if: "t'' = (If t1'' Then t2 Else t3)"
      using Cond et'' eval.cases by blast
    have "t1' = t1''" using t1_induct t1t1' t1t1'' by simp
    with t'if t''if show "t' = t''" by simp
  qed
qed


definition is_normal_form :: "t \<Rightarrow> bool"
  where "is_normal_form t \<longleftrightarrow> \<not>(\<exists>t'. t \<mapsto> t')"

lemma is_normal_formE[intro]: "\<not>(\<exists>t'. t \<mapsto> t') \<Longrightarrow> is_normal_form t" using is_normal_form_def by simp
lemma is_normal_formI[elim]: "is_normal_form t \<Longrightarrow> \<not>(\<exists>t'. t \<mapsto> t')" using is_normal_form_def by simp

lemma true_is_normal_form[intro]: "is_normal_form true" using true_cannot_eval is_normal_form_def by simp
lemma false_is_normal_form[intro]: "is_normal_form false" using false_cannot_eval is_normal_form_def by simp
lemma normal_form_cannot_eval: "\<lbrakk> is_normal_form t; t \<mapsto> t' \<rbrakk> \<Longrightarrow> False" using is_normal_form_def by blast
lemma if_isnot_normal_form: "\<not>(is_normal_form (If t1 Then t2 Else t3))"  
  apply (induct t1 arbitrary: t2 t3)
  using E_IfTrue is_normal_form_def apply blast
  using E_IfFalse is_normal_form_def apply blast
  using E_If is_normal_form_def by metis 

section \<open>3.5.7 value is normal form\<close>

(* 3.5.7 *)
theorem value_is_normal_form: "is_value t \<Longrightarrow> is_normal_form t"
  using is_value_def by fastforce

section \<open>3.5.8 normal form is value\<close>

(* 3.5.8 *)
theorem normal_form_is_value: "is_normal_form t \<Longrightarrow> is_value t"
  apply (rule t.exhaust[of t], blast, blast)
  apply (simp add: if_isnot_normal_form)
  done

section \<open>3.5.9 definition of eval*\<close>

(* 3.5.9 *)
inductive eval_star :: "t \<Rightarrow> t \<Rightarrow> bool" ("_ \<mapsto>* _" [50,50] 40) where
    EsRefl: "t \<mapsto>* t"
  | EsStep: "\<lbrakk> t \<mapsto> t' \<rbrakk> \<Longrightarrow> t \<mapsto>* t'"
  | EsTrans: "\<lbrakk> t \<mapsto>* t'; t' \<mapsto>* t'' \<rbrakk> \<Longrightarrow> t \<mapsto>* t''"

lemma eval_star_refl[intro]: "t = t' \<Longrightarrow> t \<mapsto>* t'" using EsRefl by simp
lemma eval_star_step[intro]: "t \<mapsto> t' \<Longrightarrow> t \<mapsto>* t'" by (rule EsStep)
lemma eval_star_trans1[intro]: "\<lbrakk> t \<mapsto>* t'; t' \<mapsto>* t'' \<rbrakk> \<Longrightarrow> t \<mapsto>* t''" by (rule EsTrans)
lemma eval_star_trans2[intro]: "\<lbrakk> t \<mapsto> t'; t' \<mapsto>* t'' \<rbrakk>  \<Longrightarrow> t \<mapsto>* t''" using EsStep EsTrans by blast
lemma eval_star_trans3[intro]: "\<lbrakk> t \<mapsto>* t'; t' \<mapsto> t'' \<rbrakk>  \<Longrightarrow> t \<mapsto>* t''" using EsStep EsTrans by blast

lemma eval_starI1: "\<lbrakk> t = t' \<or> t \<mapsto> t' \<or> (\<exists>t''. t \<mapsto>* t'' \<and> t'' \<mapsto>* t') \<rbrakk> \<Longrightarrow> t \<mapsto>* t'"
  using EsRefl EsStep EsTrans by blast
lemma eval_starI2: "\<lbrakk> t = t' \<or> t \<mapsto> t' \<or> (\<exists>t''. t \<mapsto>* t'' \<and> t'' \<mapsto> t') \<rbrakk> \<Longrightarrow> t \<mapsto>* t'"
  using EsRefl EsStep EsTrans by blast
lemma eval_starI3: "\<lbrakk> t = t' \<or> t \<mapsto> t' \<or> (\<exists>t''. t \<mapsto> t'' \<and> t'' \<mapsto>* t') \<rbrakk> \<Longrightarrow> t \<mapsto>* t'"
  using EsRefl EsStep EsTrans by blast

lemma E_If_star: "t1 \<mapsto>* t1' \<Longrightarrow> If t1 Then t2 Else t3 \<mapsto>* If t1' Then t2 Else t3"
proof (induct rule: eval_star.induct)
  case (EsRefl t)
  then show ?case by (rule eval_star_refl, rule refl)
next
  case (EsStep t t')
  show ?case by (rule eval_star_step, rule E_If, rule EsStep)
next
  case (EsTrans t t' t'')
  show ?case by (rule eval_star_trans1, rule EsTrans(2), rule EsTrans(4))
qed

lemma eval_star_IfTrue: "\<lbrakk> t1 \<mapsto>* true \<rbrakk> \<Longrightarrow> If t1 Then t2 Else t3 \<mapsto>* t2"
  using E_If_star[of t1, of true] E_IfTrue eval_star_trans2 eval_star_trans3 by blast

lemma eval_star_IfFalse: "\<lbrakk> t1 \<mapsto>* false \<rbrakk> \<Longrightarrow> If t1 Then t2 Else t3 \<mapsto>* t3"
  using E_If_star[of t1, of false] E_IfFalse eval_star_trans2 eval_star_trans3 by blast

lemma normal_form_eval_star_refl:
  assumes es: "t \<mapsto>* t'"
  assumes vt: "is_normal_form t"
  shows "t = t'"
  using es vt
  apply (induct rule: eval_star.induct)
    apply simp
    using normal_form_cannot_eval apply blast
    using normal_form_cannot_eval by blast

section \<open>3.5.11 deterministic of eval*\<close>

(* 3.5.11 *)
lemma eval_star_deterministic: "\<lbrakk> t \<mapsto>* t'; is_normal_form t'; t \<mapsto> t''; is_normal_form t'' \<rbrakk> \<Longrightarrow> t' = t''"
proof (induct rule: eval_star.induct)
  case (EsRefl t)
  then show ?case
    using normal_form_cannot_eval by blast 
next
  case (EsStep t t')
  then show ?case
    using eval_deterministic by blast
next
  case (EsTrans t tmid' t')
  then show ?case
    oops

section \<open>3.5.11\<^sup>* definition of eval^n\<close>

inductive eval_n :: "t \<Rightarrow> nat \<Rightarrow> t \<Rightarrow> bool" ("_ \<mapsto>^_ _" [50,90,50] 40) where
  En0: "t \<mapsto>^0 t"
| EnN: "\<lbrakk> t \<mapsto>^n t'; t' \<mapsto> t'' \<rbrakk> \<Longrightarrow> t \<mapsto>^(Suc n) t''"

lemma exist_first_step: "\<lbrakk> t \<mapsto>^(Suc n) t' \<rbrakk> \<Longrightarrow> \<exists>t''. t \<mapsto>^n t'' \<and> t'' \<mapsto> t'"
  by (metis eval_n.simps nat.inject old.nat.distinct(2))
lemma exist_mid_step: "\<lbrakk> t \<mapsto>^(n + m) t' \<rbrakk> \<Longrightarrow> \<exists>t''. t \<mapsto>^n t'' \<and> t'' \<mapsto>^m t'"
proof (induct m arbitrary: n t t')
  case 0
  then show ?case
    using En0 by auto 
next
  case (Suc m)
  then show ?case
    by (metis EnN exist_first_step nat_arith.suc1) 
qed
lemma exist_mid_step2: "\<lbrakk> t \<mapsto>^n t'; m < n \<rbrakk> \<Longrightarrow> \<exists>t''. t \<mapsto>^m t'' \<and> t'' \<mapsto>^(n - m) t'"
  using exist_mid_step by force

lemma eval_0_refl[elim]: "t \<mapsto>^0 t' \<Longrightarrow> t = t'"
  by (metis Zero_neq_Suc eval_n.simps)
lemma eval_1_step[elim]: "t \<mapsto>^1 t' \<Longrightarrow> t \<mapsto> t'"
  by (metis eval_n.simps lessI less_one nat.simps(3) one_neq_zero)
lemma eval_n_star[elim]: "t \<mapsto>^n t' \<Longrightarrow> t \<mapsto>* t'"
proof (induct rule: eval_n.induct)
  case (En0 t)
  then show ?case by (rule EsRefl)
next
  case (EnN t t' n t'')
  then show ?case by blast 
qed

lemma eval_n_plus_1: "\<lbrakk> t \<mapsto>^n t'; t' \<mapsto> t'' \<rbrakk> \<Longrightarrow> t \<mapsto>^(Suc n) t''" by (simp add: EnN)
lemma eval_n_plus_m: "\<lbrakk> t \<mapsto>^n t'; t' \<mapsto>^m t'' \<rbrakk> \<Longrightarrow> t \<mapsto>^(n+m) t''"
proof (induct m arbitrary: n t t' t'')
  case 0
  then show ?case
    using eval_0_refl by auto 
next
  case (Suc n)
  then show ?case
    by (metis eval_n.simps nat.inject nat.simps(3) nat_arith.suc1)
qed
lemma eval_1_plus_n: "\<lbrakk> t \<mapsto> t'; t' \<mapsto>^n t'' \<rbrakk> \<Longrightarrow> t \<mapsto>^(Suc n) t''"
  by (metis One_nat_def Suc_eq_plus1_left eval_n.simps eval_n_plus_m)

lemma refl_eval_0[intro]: "t = t' \<Longrightarrow> t \<mapsto>^0 t'"
  using En0 by presburger
lemma step_eval_1[intro]: "t \<mapsto> t' \<Longrightarrow> t \<mapsto>^1 t'"
  using En0 EnN by force
lemma eval_star_eval_n[intro]: "t \<mapsto>* t' \<Longrightarrow> \<exists>n. t \<mapsto>^n t'"
proof (induct rule: eval_star.induct)
  case (EsRefl t)
  then show ?case
    using En0 by blast 
next
  case (EsStep t t')
  then show ?case
    using step_eval_1 by blast 
next
  case (EsTrans t t' t'')
  then show ?case
    using eval_n_plus_m by blast 
qed

lemma can_eval_suc_inot_normal_form: "\<lbrakk> t \<mapsto>^n t'; n > 0 \<rbrakk> \<Longrightarrow> \<not>(is_normal_form t)"
  by (metis Suc_eq_plus1_left eval_1_step exist_mid_step is_normal_formI less_numeral_extra(3) not0_implies_Suc)

section \<open>3.5.11\<^sup>*\<^sup>* deterministic of eval^n\<close>

theorem eval_n_deterministic: "\<lbrakk> t \<mapsto>^n t'; t \<mapsto>^n t'' \<rbrakk> \<Longrightarrow> t' = t''"
proof (induct n arbitrary: t t' t'')
  case 0
  then show ?case
    using eval_0_refl by blast 
next
  case (Suc n)
  assume "t \<mapsto>^(Suc n) t'"
  with exist_first_step obtain tp' where tp'n:"t \<mapsto>^n tp'" and tp'next:"tp' \<mapsto> t'" by blast
  assume "t \<mapsto>^(Suc n) t''"
  with exist_first_step obtain tp'' where tp''n:"t \<mapsto>^n tp''" and tp''next:"tp'' \<mapsto> t''" by blast
  have eq:"tp' = tp''" using tp'n tp''n Suc(1) by blast
  show "t' = t''"
    using tp'next tp''next eq eval_deterministic by simp
qed

lemma eval_mid_isnot_normal_form: "\<lbrakk> t \<mapsto>^n t'; is_normal_form t'; t \<mapsto>^m t''; m < n \<rbrakk> \<Longrightarrow> \<not>(is_normal_form t'')"
proof -
  assume "t \<mapsto>^n t'" and mn: "m < n"
  then obtain t''' where pre:"t \<mapsto>^m t'''" and post:"t''' \<mapsto>^(n-m) t'" using exist_mid_step2 by blast
  have nv: "\<not>(is_normal_form t''')" apply (rule can_eval_suc_inot_normal_form[OF post]) using mn by arith
  assume "t \<mapsto>^m t''"  hence "t'' = t'''" using pre eval_n_deterministic by blast
  with nv
  show "\<not>(is_normal_form t'')" by simp
qed
lemma eval_mid_isnot_normal_form2: "\<lbrakk> t \<mapsto>^n t'; is_normal_form t'; t \<mapsto>^m t''; is_normal_form t'' \<rbrakk> \<Longrightarrow> \<not>(m < n)"
  using eval_mid_isnot_normal_form by blast

lemma eval_n_normal_exist_only_one: "\<lbrakk> t \<mapsto>^n t'; is_normal_form t'; t \<mapsto>^m t''; is_normal_form t'' \<rbrakk> \<Longrightarrow> n = m"
  using eval_mid_isnot_normal_form2[where n=n] eval_mid_isnot_normal_form2[where n=m] nat_neq_iff by blast

lemma eval_n_deterministic_on_normal_form: "\<lbrakk> t \<mapsto>^n t'; is_normal_form t'; t \<mapsto>^m t''; is_normal_form t'' \<rbrakk> \<Longrightarrow> t' = t''"
  using eval_n_normal_exist_only_one eval_n_deterministic by blast

section \<open>3.5.11 deterministic of eval*\<close>

(* 3.5.11 *)
theorem eval_star_deterministic: "\<lbrakk> t \<mapsto>* t'; is_normal_form t'; t \<mapsto>* t''; is_normal_form t'' \<rbrakk> \<Longrightarrow> t' = t''"
  apply (drule eval_star_eval_n, drule eval_star_eval_n)
  using eval_n_deterministic_on_normal_form by blast

section \<open>3.5.12 eval* halt\<close>

primrec size :: "t \<Rightarrow> nat" where
  size_true: "size true = 1"
| size_false: "size false = 1"
| size_if: "size (If t1 Then t2 Else t3) = 1 + size t1 + size t2 + size t3"

lemma normal_form_size_is_one: "is_normal_form t \<Longrightarrow> size t = 1"
proof (cases t)
  case true
  then show ?thesis by simp
next
  case false
  then show ?thesis by simp
next
  assume tv: "is_normal_form t"
  case (Cond x31 x32 x33)
  then show ?thesis using tv if_isnot_normal_form by simp
qed

lemma can_eval_size_two_or_more: "size t > 1 \<Longrightarrow> \<exists>t'. t \<mapsto> t'"
  by (metis is_normal_form_def less_numeral_extra(4) normal_form_size_is_one)

lemma size_eval_mono: "t \<mapsto> t' \<Longrightarrow> size t > size t'"
proof (induct rule: eval.induct)
  case (E_IfTrue t2 t3)
  then show ?case using size_if by arith
next
  case (E_IfFalse t2 t3)
  then show ?case using size_if by arith
next
  case (E_If t1 t1' t2 t3)
  then show ?case using size_if by arith
qed

(* 3.5.12 *)
theorem eval_star_stop: "\<exists>t'. t \<mapsto>* t' \<and> is_normal_form t'"
proof (induct t)
  case true
  then show ?case by blast 
next
  case false
  then show ?case by blast
next
  case (Cond t1 t2 t3)
  obtain t1' where t1t1': "t1 \<mapsto>* t1'" and "is_normal_form t1'" using Cond.hyps(1) by blast
  hence t1_true_false: "t1' = true \<or> t1' = false" using normal_form_is_value is_value_def by simp
  hence "If t1 Then t2 Else t3 \<mapsto>* t2 \<or> If t1 Then t2 Else t3 \<mapsto>* t3"
    using eval_star_IfTrue eval_star_IfFalse t1t1' by blast
  with Cond.hyps(2) Cond.hyps(3) eval_star_trans3 
  show "\<exists>t'. If t1 Then t2 Else t3 \<mapsto>* t' \<and> is_normal_form t'" by blast
qed