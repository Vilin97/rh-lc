module

public import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BlockDiagonalPrincipalSeriesCongruenceSubgroupSpStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTrivialOnUnitsModConductorUnitCharacterValuePrStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JacquetKernelEigenvectorEqZeroOfConstCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JacquetModuleMaximalParabolicPrincipalSeriesTypeStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterBlockDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterEqOneNearOneStatement
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.NumberTheory.LocalField.Basic
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedJacquetSurvivalProductOfTwoGroupsStatement
import Mathlib.Topology.Algebra.Group.Units

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrderedCharacterFamilySplitsOrConstantOnUnits

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem apply_eq_one_of_triv_one_unit {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {χ : kˣ →* ℂˣ} (h : Triv χ 1) (u : kˣ) (hu : valuation k (u : k) = 1) : χ u = 1 := by
  apply h u hu
  calc valuation k ((u : k) - 1) ≤ max (valuation k (u : k)) (valuation k 1) := Valuation.map_sub _ _ _
    _ = valuation k 1 := by simp [hu]

theorem cut_or_const : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → (∃ r : ℕ, 0 < r ∧ r < n ∧ Cut ψ r) ∨ ∃ χ : kˣ →* ℂˣ, ((∀ i, IsSmoothChar (ψ i)) → IsSmoothChar χ) ∧ Agree ψ (fun _ => χ) := by
  intro k _ _ _ _ n ψ hord
  by_cases hc : ∃ m : ℕ, ∃ h : m + 1 < n, ¬ Triv (ψ ⟨m, by omega⟩ / ψ ⟨m + 1, h⟩) 1
  · obtain ⟨m, hm, hnt⟩ := hc
    refine Or.inl ⟨m + 1, by omega, hm, ?_⟩
    intro i j hi hj htr
    have h1 : i ≤ (⟨m, by omega⟩ : Fin n) := by rw [Fin.le_def]; simp; omega
    have h2 : (⟨m, by omega⟩ : Fin n) ≤ ⟨m + 1, hm⟩ := by rw [Fin.le_def]; simp
    have h3 : (⟨m + 1, hm⟩ : Fin n) ≤ j := by rw [Fin.le_def]; simp; omega
    exact hnt (hord i _ _ j h1 h2 h3 1 htr)
  · push_neg at hc
    right
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      refine ⟨1, fun _ => ?_, fun i => i.elim0⟩
      show IsOpen ((1 : kˣ →* ℂˣ).ker : Set kˣ)
      simp
    · refine ⟨ψ ⟨0, hn⟩, fun hs => hs _, ?_⟩
      have key : ∀ m (hm : m < n) (u : kˣ), valuation k (u : k) = 1 → ψ ⟨m, hm⟩ u = ψ ⟨0, hn⟩ u := by
        intro m
        induction m with
        | zero => intro _ _ _; rfl
        | succ m ih =>
          intro hm u hu
          have h1 := apply_eq_one_of_triv_one_unit (hc m hm) u hu
          rw [MonoidHom.div_apply, div_eq_one] at h1
          rw [← h1, ih (by omega) u hu]
      intro i u hu
      exact key i.1 i.2 u hu

end GlobalTheory.PsType
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrderedCharacterFamilySplitsOrConstantOnUnitsStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.orderedCharacterFamily_splits_or_constant_on_units : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → (∃ r : ℕ, 0 < r ∧ r < n ∧ Cut ψ r) ∨ ∃ χ : kˣ →* ℂˣ, ((∀ i, IsSmoothChar (ψ i)) → IsSmoothChar χ) ∧ Agree ψ (fun _ => χ) := by
  first | exact @GlobalTheory.PsType.cut_or_const | exact GlobalTheory.PsType.cut_or_const | (intros; apply GlobalTheory.PsType.cut_or_const <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeDataDependOnlyOnUnits

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem agree_div_apply {ψ ω : Fin n → kˣ →* ℂˣ} (h : Agree ψ ω) (i j : Fin n) (u : kˣ)
    (hu : valuation k (u : k) = 1) : (ψ i / ψ j) u = (ω i / ω j) u := by
  simp only [MonoidHom.div_apply, h i u hu, h j u hu]

theorem agree_triv_iff {ψ ω : Fin n → kˣ →* ℂˣ} (h : Agree ψ ω) (i j : Fin n) (x : k) :
    Triv (ψ i / ψ j) x ↔ Triv (ω i / ω j) x := by
  constructor
  · intro H u hu hx
    rw [← agree_div_apply h i j u hu]
    exact H u hu hx
  · intro H u hu hx
    rw [agree_div_apply h i j u hu]
    exact H u hu hx

theorem agree_nxt_apply {ψ ω : Fin n → kˣ →* ℂˣ} (h : Agree ψ ω) (m : Fin n) (u : kˣ)
    (hu : valuation k (u : k) = 1) : nxt ψ m u = nxt ω m u := by
  unfold nxt
  split_ifs
  · exact h _ u hu
  · rfl

theorem agree_ev {ψ ω : Fin n → kˣ →* ℂˣ} (h : Agree ψ ω) (m : Fin n) (x : k) :
    ev (ψ m / nxt ψ m) x = ev (ω m / nxt ω m) x := by
  unfold ev
  split_ifs with hx
  · have hv : valuation k ((Units.mk0 x fun h0 => by simp [h0] at hx : kˣ) : k) = 1 := by
      simpa using hx
    rw [MonoidHom.div_apply, MonoidHom.div_apply, h m _ hv, agree_nxt_apply h m _ hv]
  · rfl

theorem agree_main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (ψ ω : Fin n → kˣ →* ℂˣ), Agree ψ ω → grp ψ = grp ω ∧ theta ψ = theta ω ∧ (Ordered ψ → Ordered ω) ∧
      ∀ r, Cut ψ r → Cut ω r := by
  intro k _ _ _ _ n ψ ω h
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext g
    simp only [grp, Set.mem_setOf_eq, agree_triv_iff h]
  · funext g
    unfold theta
    exact Finset.prod_congr rfl fun m _ => agree_ev h m _
  · intro H i a b j hi ha hb x hT
    rw [← agree_triv_iff h]
    exact H i a b j hi ha hb x ((agree_triv_iff h i j x).2 hT)
  · intro r H i j hi hj hT
    exact H i j hi hj ((agree_triv_iff h i j 1).2 hT)

end GlobalTheory.PsType
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeDataDependOnlyOnUnitsStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.principalSeriesType_data_depend_only_on_units : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ ω : Fin n → kˣ →* ℂˣ), Agree ψ ω → grp ψ = grp ω ∧ theta ψ = theta ω ∧ (Ordered ψ → Ordered ω) ∧ ∀ r, Cut ψ r → Cut ω r := by
  first | exact @GlobalTheory.PsType.agree_main | exact GlobalTheory.PsType.agree_main | (intros; apply GlobalTheory.PsType.agree_main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedJacquetKernelTwoBlockUnipotentLeStages

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem twKer_unipB_le_of_stages : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (r + t)) k) V) (P : Submodule ℂ V), twKer π (unipRad k (two (stdSum (rfl : r + t = r + t)))) 1 ≤ P → (∀ u ∈ unipB k (Fin r), ∀ w, π (emb₂ k (stdSum (rfl : r + t = r + t)) (u, 1)) w - w ∈ P) → (∀ u ∈ unipB k (Fin t), ∀ w, π (emb₂ k (stdSum (rfl : r + t = r + t)) (1, u)) w - w ∈ P) → twKer π (unipB k (Fin (r + t))) 1 ≤ P := by
  intro k _ _ _ _ r t V _ _ π P h0 h1 h2
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨u, hu⟩, w, rfl⟩
  set e := stdSum (rfl : r + t = r + t) with he
  obtain ⟨hl, hd⟩ := (mem_unipB k).1 hu
  have hp : u ∈ parab k (two e) := (mem_parab_two k).2 fun j i => hl _ _ (by
    rw [Fin.lt_def, he, stdSum_inl, stdSum_inr]; omega)
  obtain ⟨y, hy, hdec⟩ := exists_levi_mul_unip k (two e) ⟨u, hp⟩
  set a : GL (Fin r) k := leviProj k (two e) ⟨u, hp⟩ false with ha
  set b : GL (Fin t) k := leviProj k (two e) ⟨u, hp⟩ true with hb
  have hau : a ∈ unipB k (Fin r) := (mem_unipB k).2 ⟨fun i j hij => hl (e (.inl i)) (e (.inl j)) (by
    rw [Fin.lt_def, he, stdSum_inl, stdSum_inl]; exact hij), fun i => hd (e (.inl i))⟩
  have hbu : b ∈ unipB k (Fin t) := (mem_unipB k).2 ⟨fun i j hij => hl (e (.inr i)) (e (.inr j)) (by
    rw [Fin.lt_def, he, stdSum_inr, stdSum_inr]; exact Nat.add_lt_add_left hij r), fun i => hd (e (.inr i))⟩
  have hlev : leviEmb k (two e) (leviProj k (two e) ⟨u, hp⟩) = emb₂ k e (a, 1) * emb₂ k e (1, b) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    show _ = leviEmb k (two e) (leviTwo k _ _ (a, b))
    congr 1
    funext x
    cases x <;> rfl
  have hdec' : u = emb₂ k e (a, 1) * emb₂ k e (1, b) * y := by rw [← hlev]; exact hdec
  have h3 : π y w - w ∈ P := h0 (Submodule.subset_span ⟨⟨y, hy⟩, w, by simp⟩)
  have h4 := P.add_mem (P.add_mem (h1 a hau (π (emb₂ k e (1, b)) (π y w))) (h2 b hbu (π y w))) h3
  have h5 : π u w - w ∈ P := by
    rw [hdec', map_mul, map_mul]
    simpa using h4
  simpa using h5

end GlobalTheory.PsType
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedJacquetKernelTwoBlockUnipotentLeStagesStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.twistedJacquetKernel_twoBlock_unipotent_le_stages : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (r + t)) k) V) (P : Submodule ℂ V), twKer π (unipRad k (two (stdSum (rfl : r + t = r + t)))) 1 ≤ P → (∀ u ∈ unipB k (Fin r), ∀ w, π (emb₂ k (stdSum (rfl : r + t = r + t)) (u, 1)) w - w ∈ P) → (∀ u ∈ unipB k (Fin t), ∀ w, π (emb₂ k (stdSum (rfl : r + t = r + t)) (1, u)) w - w ∈ P) → twKer π (unipB k (Fin (r + t))) 1 ≤ P := by
  first | exact @GlobalTheory.PsType.twKer_unipB_le_of_stages | exact GlobalTheory.PsType.twKer_unipB_le_of_stages | (intros; apply GlobalTheory.PsType.twKer_unipB_le_of_stages <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfMemTwistedJacquetKernelUpperUnitriangula

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem eq_zero_of_mem_twKer_unipB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → ∀ v ∈ twKer π (unipB k (Fin n)) 1, IsEig π (grp ψ) (theta ψ) v → v = 0 := by
  intro k _ _ _ _ n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ψ V _ _ π hπ hψ hord v hv heig
  rcases GlobalTheory.T.orderedCharacterFamily_splits_or_constant_on_units k n ψ hord with ⟨r, hr0, hrn, hcut⟩ | ⟨χ, hχ, hag⟩
  swap
  · obtain ⟨hg, hth, -, -⟩ := GlobalTheory.T.principalSeriesType_data_depend_only_on_units k n ψ _ hag
    rw [hg, hth] at heig
    exact GlobalTheory.T.jacquetKernel_eigenvector_eq_zero_of_const_character k n χ V π hπ (hχ hψ) v hv heig
  obtain ⟨t, rfl⟩ : ∃ t, n = r + t := ⟨n - r, by omega⟩
  have ht : 0 < t := by omega
  set e := stdSum (rfl : r + t = r + t) with he
  set ψ₁ : Fin r → kˣ →* ℂˣ := fun i => ψ (Fin.castAdd t i) with hψ₁
  set ψ₂ : Fin t → kˣ →* ℂˣ := fun i => ψ (Fin.natAdd r i) with hψ₂
  obtain ⟨ho₁, ho₂, hmem⟩ := GlobalTheory.T.blockDiagonal_principalSeriesCongruenceSubgroup_split k r t ψ hord hcut
  have hs₁ : ∀ i, IsSmoothChar (ψ₁ i) := fun i => hψ _
  have hs₂ : ∀ i, IsSmoothChar (ψ₂ i) := fun i => hψ _
  have one_grp : ∀ (m : ℕ) (φ : Fin m → kˣ →* ℂˣ), (1 : GL (Fin m) k) ∈ grp φ := by
    intro m φ
    refine ⟨(KO k (Fin m)).one_mem, fun i j hij => ?_⟩
    have h0 : ((1 : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) i j = 0 := by
      simp [Matrix.one_apply_ne (ne_of_lt hij)]
    rw [h0]
    exact (GlobalTheory.T.isTrivialOnUnitsModConductor_unitCharacterValue_props k).2.2.1 _
  let Q := twKer π (unipRad k (two e)) 1
  let ρ := jacU₂ e π
  have hρ : IsSmooth ρ := isSmooth_comp (isSmooth_jacU _ hπ) _ (continuous_leviTwo k)
  have hact : ∀ g w, ρ g (Q.mkQ w) = Q.mkQ (π (emb₂ k e g) w) := fun g w => rfl
  let P : Submodule ℂ V := (twKer (ρ.comp (MonoidHom.inl _ _)) (unipB k (Fin r)) 1 ⊔
      twKer (ρ.comp (MonoidHom.inr _ _)) (unipB k (Fin t)) 1).comap Q.mkQ
  have hP : twKer π (unipB k (Fin (r + t))) 1 ≤ P := by
    refine GlobalTheory.T.twistedJacquetKernel_twoBlock_unipotent_le_stages k r t V π P ?_ ?_ ?_
    · intro w hw
      refine Submodule.mem_comap.2 ?_
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero Q).2 hw]
      exact zero_mem _
    · intro u hu w
      refine Submodule.mem_comap.2 ?_
      refine Submodule.mem_sup_left (Submodule.subset_span ⟨⟨u, hu⟩, Q.mkQ w, ?_⟩)
      simp only [map_sub, MonoidHom.one_apply, Units.val_one, one_smul, Submodule.mkQ_apply]
      rfl
    · intro u hu w
      refine Submodule.mem_comap.2 ?_
      refine Submodule.mem_sup_right (Submodule.subset_span ⟨⟨u, hu⟩, Q.mkQ w, ?_⟩)
      simp only [map_sub, MonoidHom.one_apply, Units.val_one, one_smul, Submodule.mkQ_apply]
      rfl
  have hx := hP hv
  have hzero : Q.mkQ v = 0 := by
    refine GlobalTheory.T.twistedJacquet_survival_product_of_two_groups (GL (Fin r) k) (GL (Fin t) k) _ ρ hρ (unipB k (Fin r)) (unipB k (Fin t))
      (grp ψ₁) (grp ψ₂) (theta ψ₁) (theta ψ₂)
      (fun W _ _ σ hσ w hw hwe => ih r (by omega) ψ₁ W σ hσ hs₁ ho₁ w hw hwe)
      (fun W _ _ σ hσ w hw hwe => ih t (by omega) ψ₂ W σ hσ hs₂ ho₂ w hw hwe)
      (Q.mkQ v) hx ?_ ?_
    · intro a ha
      have hm : emb₂ k e (a, 1) ∈ grp ψ := (hmem a 1).2 ⟨ha, one_grp _ _⟩
      have hth := GlobalTheory.T.principalSeriesTypeCharacter_blockDiagonal k r t ψ hord a ha 1 (one_grp _ _)
      rw [(GlobalTheory.T.principalSeriesTypeCharacter_eq_one_near_one k t ψ₂ hs₂).1, mul_one] at hth
      show ρ (a, 1) (Q.mkQ v) = _
      rw [hact, heig _ hm, map_smul]
      exact congrArg (· • Q.mkQ v) hth
    · intro b hb
      have hm : emb₂ k e (1, b) ∈ grp ψ := (hmem 1 b).2 ⟨one_grp _ _, hb⟩
      have hth := GlobalTheory.T.principalSeriesTypeCharacter_blockDiagonal k r t ψ hord 1 (one_grp _ _) b hb
      rw [(GlobalTheory.T.principalSeriesTypeCharacter_eq_one_near_one k r ψ₁ hs₁).1, one_mul] at hth
      show ρ (1, b) (Q.mkQ v) = _
      rw [hact, heig _ hm, map_smul]
      exact congrArg (· • Q.mkQ v) hth
  have hvQ : v ∈ Q := (Submodule.Quotient.mk_eq_zero Q).1 hzero
  exact GlobalTheory.T.jacquetModule_maximalParabolic_principalSeriesTypeEigen k r t ψ V π hπ hψ hord hcut v hvQ heig

end GlobalTheory.PsType
end
end
