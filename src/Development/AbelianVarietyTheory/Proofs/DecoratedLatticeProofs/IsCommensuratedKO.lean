module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeOperatorMoveAcrossInvariantBilinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLeCard
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.CommensuratedOfIsOpenIsCompact
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FiniteCosetsInDoset
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumSphericalFunctionDoublingLength
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BiInvariantReplaceSameDoubleCosetSums
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightInvariantEqSumOpenSubgroupCosets
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Topology.Algebra.Group.Units

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBorelSphericalSameDoubleCosetSumsZonal

section

@[expose] public section

open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

noncomputable section

namespace GlobalTheory.ZonalBorel

open GlobalTheory.PRep Formalism.UG

section Abstract

variable {G X V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup V] [Module ℂ V]

theorem exists_fixed_sum_eq {ρ : Representation ℂ G X} {π : Representation ℂ G V} (hρ : IsSmooth ρ)
    {K : Subgroup G} (hK : IsCompact (K : Set G)) (f : ρ.IntertwiningMap π) (hf : Function.Surjective f)
    (E : X →ₗ[ℂ] ℂ) (hE : ∀ u : X, (∀ x ∈ K, ρ x u = u) → E u = 0 → u = 0) {v : V} (hv : v ∈ fixed π K)
    (l : Module.Dual ℂ V) (hlv : l v = 1) :
    ∃ z : X, (∀ x ∈ K, ρ x z = z) ∧ E z = 1 ∧ ∀ S : Finset (G ⧸ K), (∀ x ∈ K, ∀ c ∈ S, x • c ∈ S) →
      ∑ c ∈ S, l (π c.out v) = ∑ c ∈ S, E (ρ c.out z) := by
  obtain ⟨u, rfl⟩ := hf v
  obtain ⟨w, hw, hfw⟩ := IwahoriOnto.exists_fixed_map_eq hρ hK f.toLinearMap u fun h hh => by
    show f (ρ h u) = f u
    rw [f.isIntertwining]
    simpa using hv ⟨h, hh⟩
  have hw' : ∀ x ∈ K, ρ x w = w := fun x hx => by simpa using hw ⟨x, hx⟩
  have hfw' : f w = f u := hfw
  have hEw : E w ≠ 0 := fun h => by
    have h0 := hE w hw' h
    rw [h0, map_zero] at hfw'
    rw [← hfw', map_zero] at hlv
    exact zero_ne_one hlv
  refine ⟨(E w)⁻¹ • w, fun x hx => by rw [map_smul, hw' x hx], by simp [hEw], fun S hS => ?_⟩
  set z := (E w)⁻¹ • w with hz
  have hzK : ∀ x ∈ K, ρ x z = z := fun x hx => by rw [hz, map_smul, hw' x hx]
  have hEz : E z = 1 := by simp [hz, hEw]
  have hfz : f z = (E w)⁻¹ • f u := by rw [hz, map_smul, hfw']
  have h1 := hE (∑ c ∈ S, ρ c.out z - (∑ c ∈ S, E (ρ c.out z)) • z)
    (fun x hx => by rw [map_sub, Rep.sum_fixed ρ K hzK S hS x hx, map_smul, hzK x hx])
    (by rw [map_sub, map_sum, map_smul, hEz, smul_eq_mul, mul_one, sub_self])
  have h2 := congrArg (fun y => l (f y)) (sub_eq_zero.1 h1)
  have hI : ∀ c : G ⧸ K, f (ρ c.out z) = π c.out (f z) := fun c => f.isIntertwining _ _ _ _

  simp only [map_sum, map_smul, hI, hfz, smul_eq_mul, hlv, mul_one] at h2
  rw [← Finset.mul_sum] at h2
  exact (mul_right_injective₀ (inv_ne_zero hEw)).eq_iff.1 (h2.trans (mul_comm _ _))

end Abstract

theorem exists_isBorelSph_hAct_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (α : Fin n → ℂˣ), HasSatake π α → ∀ ω : GL (Fin n) k → ℂ, IsZonal π (KO k (Fin n)) ω → ∃ φ : GL (Fin n) k → ℂ, IsBorelSph k (fun i : Fin n => (α i : ℂ) * (((resCard k : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ)) φ ∧ ∀ g, Formalism.UG.hAct (KO k (Fin n)) (Formalism.UG.dosetInd ℂ (KO k (Fin n)) g) ω 1 = Formalism.UG.hAct (KO k (Fin n)) (Formalism.UG.dosetInd ℂ (KO k (Fin n)) g) φ 1 := by
  intro k _ _ _ _ n V _ _ π α ⟨_, _hs, S, f, hf⟩ ω ⟨v, hv, l, _hl, hlv, hω⟩
  have hsm : IsSmooth S.toRepresentation :=
    IsSubquotient.isSmooth ⟨S, .id _, Function.surjective_id⟩ (isSmooth_parInd _ _)
  let E : S.toSubmodule →ₗ[ℂ] ℂ := ⟨⟨fun u => u.1.1.1 1, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  have hr : ∀ u : S.toSubmodule, (∀ x ∈ KO k (Fin n), S.toRepresentation x u = u) →
      ∀ g, ∀ x ∈ KO k (Fin n), u.1.1.1 (g * x) = u.1.1.1 g := fun u h g x hx =>
    congrArg (fun z : S.toSubmodule => z.1.1.1 g) (h x hx)
  obtain ⟨z, hzK, hEz, key⟩ := exists_fixed_sum_eq hsm SplitFlip.isCompact_KO f hf E (fun u h h0 => by
    refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun g => ?_)))
    obtain ⟨b, hb, x, hx, rfl⟩ := iwasawa_blockTriangular k (Fin n) Fin.val g
    have h1 := parInd_law _ _ u.1 ⟨b, (mem_borel _).2 hb⟩ 1
    have h2 : u.1.1.1 1 = 0 := h0
    rw [h2, map_zero, smul_zero, mul_one] at h1
    exact (hr u h b x hx).trans h1) hv l hlv
  refine ⟨fun g => z.1.1.1 g, ⟨hr z hzK, fun b hb t ht => ?_⟩, fun g => ?_⟩
  · have h1 := Rep.law α z.1 b hb t ht 1
    have h2 : z.1.1.1 1 = 1 := hEz
    rwa [h2, mul_one, mul_one] at h1
  · have hK : IsCommensurated (KO k (Fin n)) :=
      PI.UnitaryGroupMassFormula.AdIndexEq.commensurated_of_isOpen_isCompact _ SplitFlip.isOpen_KO SplitFlip.isCompact_KO
    have hfin := Formalism.UG.P.finite_support_cosets hK (Formalism.UG.Final.DosetIndMem _ (KO k (Fin n)) ℂ g).2
    have hmem : ∀ c : GL (Fin n) k ⧸ KO k (Fin n), c ∈ hfin.toFinset ↔
        c.out ∈ DoubleCoset.doubleCoset g (KO k (Fin n) : Set (GL (Fin n) k)) (KO k (Fin n)) := fun c => by
      simp [dosetInd]
    have hT : ∀ x ∈ KO k (Fin n), ∀ c ∈ hfin.toFinset, x • c ∈ hfin.toFinset := by
      intro x hx c hc
      obtain ⟨a, ha, rfl⟩ := (GlobalTheory.ChainOnto.out_mem_doubleCoset_iff g c).1 ((hmem c).1 hc)
      refine (hmem _).2 ((GlobalTheory.ChainOnto.out_mem_doubleCoset_iff g _).2 ⟨x * a, mul_mem hx ha, ?_⟩)
      rw [mul_assoc]
      rfl
    have e : ∀ F : GL (Fin n) k → ℂ, hAct (KO k (Fin n)) (dosetInd ℂ (KO k (Fin n)) g) F 1 =
        ∑ c ∈ hfin.toFinset, F c.out := by
      intro F
      rw [hAct, finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
      · refine Finset.sum_congr rfl fun c hc => ?_
        rw [dosetInd, Set.indicator_of_mem ((hmem c).1 hc), one_mul, Pi.one_apply, one_smul]
      · intro c hc
        rw [Function.mem_support] at hc
        refine (hmem c).2 ?_
        by_contra h
        rw [dosetInd, Set.indicator_of_notMem h, zero_smul] at hc
        exact hc rfl
    rw [e, e]
    refine ((Finset.sum_congr rfl fun c _ => hω c.out).trans (key _ hT)).trans
      (Finset.sum_congr rfl fun c _ => ?_)
    show z.1.1.1 (1 * c.out) = _
    rw [one_mul]

end GlobalTheory.ZonalBorel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBorelSphericalSameDoubleCosetSumsZonalStatement

section

@[expose] public section

open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling


theorem _root_.GlobalTheory.T.exists_borel_spherical_same_double_coset_sums_zonal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (α : Fin n → ℂˣ), HasSatake π α → ∀ ω : GL (Fin n) k → ℂ, IsZonal π (KO k (Fin n)) ω → ∃ φ : GL (Fin n) k → ℂ, IsBorelSph k (fun i : Fin n => (α i : ℂ) * (((resCard k : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ)) φ ∧ ∀ g, Formalism.UG.hAct (KO k (Fin n)) (Formalism.UG.dosetInd ℂ (KO k (Fin n)) g) ω 1 = Formalism.UG.hAct (KO k (Fin n)) (Formalism.UG.dosetInd ℂ (KO k (Fin n)) g) φ 1 := by
  first | exact @GlobalTheory.ZonalBorel.exists_isBorelSph_hAct_eq | exact GlobalTheory.ZonalBorel.exists_isBorelSph_hAct_eq | (intros; apply GlobalTheory.ZonalBorel.exists_isBorelSph_hAct_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumSphericalFunctionDoublingLengthStatement

section

@[expose] public section

open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling


theorem _root_.GlobalTheory.T.hasSum_sphericalFunction_doublingLength : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ), IsBorelSph k γ φ → (∀ i, γ i ≠ 0) → ∀ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k → ∀ len : GL (Fin n) k → ℕ, (∀ e : Fin n → ℤ, Antitone e → ∀ g ∈ cell k (Fin n) ϖ e, len g = (∑ i, |e i|).toNat) → ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℂ, ‖X‖ < δ → HasSum (fun c : GL (Fin n) k ⧸ KO k (Fin n) => X ^ len c.out * φ c.out) ((∏ i : Fin n, (1 - (resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X)⁻¹) * (∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X)⁻¹) * ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2)) := by
  first | exact @GlobalTheory.DoublingLength.hasSum_doublingLength | exact GlobalTheory.DoublingLength.hasSum_doublingLength | (intros; apply GlobalTheory.DoublingLength.hasSum_doublingLength <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCommensuratedKO

section

@[expose] public section

noncomputable section

open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

namespace GlobalTheory.UnramDoublingProof

section Cells

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_cell {N : ℕ} {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (g : GL (Fin N) k) :
    ∃ e : {e : Fin N → ℤ // Antitone e}, g ∈ cell k (Fin N) ϖ e := by
  have h := iUnion_cell (k := k) (N := N) hϖ
  exact Set.mem_iUnion.1 (h ▸ Set.mem_univ g)

def cellLen {N : ℕ} {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (g : GL (Fin N) k) : ℕ :=
  (∑ i, |(exists_cell hϖ g).choose.1 i|).toNat

theorem cellLen_eq {N : ℕ} {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (e : Fin N → ℤ) (he : Antitone e)
    (g : GL (Fin N) k) (hg : g ∈ cell k (Fin N) ϖ e) : cellLen hϖ g = (∑ i, |e i|).toNat := by
  have h := (exists_cell hϖ g).choose_spec
  have h' : (exists_cell hϖ g).choose = ⟨e, he⟩ := by
    by_contra hne
    exact Set.disjoint_left.1 (pairwise_disjoint_cell hϖ hne) h hg
  simp only [cellLen, h']

theorem sphSection_eq_pow {N : ℕ} {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : ℂ)
    (g : GL (Fin N) k) :
    sphSection k (Fin N) s (io k (Fin N) (g, 1)) =
      ((resCard k : ℂ) ^ (-((N : ℂ) / 2 + s))) ^ cellLen hϖ g := by
  obtain ⟨⟨e, he⟩, hg⟩ := exists_cell hϖ g
  rw [cellLen_eq hϖ e he g hg]
  obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
  rw [sphSection_io_biinv s _ hx hy, sphSection_torusElt hϖ, Fintype.card_fin, ← Complex.cpow_nat_mul]
  have h0 : 0 ≤ ∑ i, |e i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hc : (((∑ i, |e i|).toNat : ℕ) : ℂ) = ((∑ i, |e i| : ℤ) : ℂ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
  rw [hc]
  congr 1
  ring

theorem isCommensurated_KO {N : ℕ} : Formalism.UG.IsCommensurated (KO k (Fin N)) := by
  intro x
  have hmo : IsOpen (((KO k (Fin N)).map (MulAut.conj x).toMonoidHom : Subgroup (GL (Fin N) k)) :
      Set (GL (Fin N) k)) := by
    have hset : (((KO k (Fin N)).map (MulAut.conj x).toMonoidHom : Subgroup (GL (Fin N) k)) :
        Set (GL (Fin N) k)) = (fun y => x⁻¹ * y * x) ⁻¹' (KO k (Fin N) : Set (GL (Fin N) k)) := by
      ext y
      simp only [Subgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa [mul_assoc] using hz
      · intro h
        exact ⟨_, h, by group⟩
    rw [hset]
    exact SplitFlip.isOpen_KO.preimage (by fun_prop)
  have : CompactSpace (KO k (Fin N)) := isCompact_iff_compactSpace.mp SplitFlip.isCompact_KO
  have hso : IsOpen ((((KO k (Fin N)).map (MulAut.conj x).toMonoidHom).subgroupOf (KO k (Fin N)) :
      Subgroup (KO k (Fin N))) : Set (KO k (Fin N))) := by
    rw [Subgroup.coe_subgroupOf]
    exact hmo.preimage continuous_subtype_val
  have : Finite ((KO k (Fin N)) ⧸ ((KO k (Fin N)).map (MulAut.conj x).toMonoidHom).subgroupOf (KO k (Fin N))) :=
    Subgroup.quotient_finite_of_isOpen _ hso
  exact Subgroup.index_ne_zero_of_finite

end Cells

section Factors

theorem factor_one {q n : ℕ} (hq : 0 < q) (i : Fin n) (a s : ℂ) :
    (q : ℂ) ^ (n - 1 - (i : ℕ)) * (a * (((q : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ)) *
      (q : ℂ) ^ (-((n : ℂ) / 2 + s)) = a * (q : ℂ) ^ (-(s + 1 / 2)) := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  have hc : ((n - 1 - (i : ℕ) : ℕ) : ℂ) = (n : ℂ) - 1 - (i : ℕ) := by
    have := i.2
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast, ← Complex.cpow_natCast, hc,
    mul_left_comm, mul_assoc, ← Complex.cpow_add _ _ hq0, ← Complex.cpow_add _ _ hq0]
  congr 2
  push_cast
  ring

theorem qpow_mul_inv_mul_qpow_eq {q n : ℕ} (hq : 0 < q) (i : Fin n) (a s : ℂ) :
    (q : ℂ) ^ (i : ℕ) * (a * (((q : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ))⁻¹ *
      (q : ℂ) ^ (-((n : ℂ) / 2 + s)) = a⁻¹ * (q : ℂ) ^ (-(s + 1 / 2)) := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast, ← Complex.cpow_natCast, mul_inv,
    ← Complex.cpow_neg, mul_left_comm, mul_assoc, ← Complex.cpow_add _ _ hq0, ← Complex.cpow_add _ _ hq0]
  congr 2
  push_cast
  ring

theorem prod_one_sub_eq_invNormFactor {q n : ℕ} (hq : 0 < q) (s : ℂ) :
    ∏ i : Fin n, (1 - (q : ℂ) ^ (i : ℕ) * ((q : ℂ) ^ (-((n : ℂ) / 2 + s))) ^ 2) = invNormFactor q n s := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  unfold invNormFactor
  refine Finset.prod_bij' (fun i _ => n - (i : ℕ))
    (fun j hj => ⟨n - j, by have := Finset.mem_Icc.1 hj; omega⟩) (fun i _ => ?_) (fun _ _ => Finset.mem_univ _)
    (fun i _ => ?_) (fun j hj => ?_) (fun i _ => ?_)
  · have := i.2
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  · have := i.2
    exact Fin.ext (by simp only; omega)
  · have := Finset.mem_Icc.1 hj
    simp only
    omega
  · rw [← Complex.cpow_nat_mul, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hq0, Nat.cast_sub i.2.le]
    congr 2
    push_cast
    ring

end Factors

theorem unramifiedDoublingGL : GlobalTheory.Published.UnramifiedDoublingGL := by
  intro k _ _ _ _ _ n _ _ μ _ hμ V _ _ π α hπ ω hω
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
    obtain ⟨x, hx⟩ := valuation_surjective (K := k) (uniformizer k)
    have h0 : x ≠ 0 := by
      rintro rfl
      exact uniformizer_ne_zero (R := k) (by simpa using hx.symm)
    exact ⟨Units.mk0 x h0, hx⟩
  have hq1 : 1 < resCard k := one_lt_resCard k
  have hq : 0 < resCard k := zero_lt_one.trans hq1
  have hqR : (1 : ℝ) < resCard k := by exact_mod_cast hq1
  have hqR0 : (0 : ℝ) < resCard k := zero_lt_one.trans hqR
  obtain ⟨φ, hφ, hsum⟩ := GlobalTheory.T.exists_borel_spherical_same_double_coset_sums_zonal k n V π α hπ ω hω
  obtain ⟨δ, hδ, hmain⟩ := GlobalTheory.T.hasSum_sphericalFunction_doublingLength k n _ φ hφ
    (fun i => mul_ne_zero (α i).ne_zero (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hqR0 _).ne'))
    ϖ hϖ (cellLen hϖ) (cellLen_eq hϖ)
  refine ⟨-Real.logb (resCard k) δ - n / 2, fun s hs => ?_⟩
  have hX : ‖(resCard k : ℂ) ^ (-((n : ℂ) / 2 + s))‖ < δ := by
    rw [Complex.norm_natCast_cpow_of_pos hq]
    refine (Real.rpow_lt_rpow_of_exponent_lt hqR (?_ : _ < Real.logb (resCard k) δ)).trans_eq
      (Real.rpow_logb hqR0 hqR.ne' hδ)
    have : (-((n : ℂ) / 2 + s)).re = -((n : ℝ) / 2 + s.re) := by simp
    rw [this]
    linarith
  have h1 := hmain _ hX
  simp only [← sphSection_eq_pow hϖ s, factor_one hq, qpow_mul_inv_mul_qpow_eq hq, prod_one_sub_eq_invNormFactor hq] at h1
  have h2 := GlobalTheory.InertZeta.dosetSwap (GL (Fin n) k) (KO k (Fin n)) isCommensurated_KO
    (fun g => sphSection k (Fin n) s (io k (Fin n) (g, 1))) ω φ _
    (fun a b g => sphSection_io_biinv s g a.2 b.2) (fun a b g => zonal_biinv hω g a.2 b.2) hsum h1
  have h3 := GlobalTheory.InertZeta.cosetIntegral_holds (GL (Fin n) k) μ (KO k (Fin n)) SplitFlip.isOpen_KO hμ
    (fun g => sphSection k (Fin n) s (io k (Fin n) (g, 1)) * ω g) _ (fun g y hy => by
      have e1 := sphSection_io_biinv s g (one_mem (KO k (Fin n))) hy
      have e2 := zonal_biinv hω g (one_mem (KO k (Fin n))) hy
      rw [one_mul] at e1 e2
      simp only [e1, e2]) h2
  refine ⟨h3.1, h3.2.trans ?_⟩
  simp only [lFactor, Pi.inv_apply, Units.val_inv_eq_inv_val]

end GlobalTheory.UnramDoublingProof
end
end
end
