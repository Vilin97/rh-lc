module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitCompletelyPlaceStructure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalHermitianDualQuotientCyclicSplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceLatticeComponents
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitIntLoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualLatticeLocalCharacterization
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLatticeVectorApproxAllFinitePlaces
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceDualQuotientComponentsIffStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimeSqLeLocalHermitianDualIndex

section

@[expose] public section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.IdxLower

theorem prime_le_relIndex {G : Type*} [AddCommGroup G] (H K : AddSubgroup G) (T : ℕ) (hT : T.Prime)
    (h0 : H.relIndex K ≠ 0) (hk : ∃ k ∈ K, k ∉ H) (hkill : ∀ k ∈ K, T • k ∈ H) :
    T ≤ H.relIndex K := by
  classical
  obtain ⟨k, hkK, hkH⟩ := hk
  have hq0 : (((⟨k, hkK⟩ : K) : K ⧸ H.addSubgroupOf K)) ≠ 0 := by
    intro h
    apply hkH
    have := (QuotientAddGroup.eq_zero_iff _).1 h
    simpa [AddSubgroup.mem_addSubgroupOf] using this
  have hqT : T • (((⟨k, hkK⟩ : K) : K ⧸ H.addSubgroupOf K)) = 0 := by
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    simpa using hkill k hkK
  have hord : addOrderOf (((⟨k, hkK⟩ : K) : K ⧸ H.addSubgroupOf K)) = T := by
    rcases hT.eq_one_or_self_of_dvd _ (addOrderOf_dvd_of_nsmul_eq_zero hqT) with h | h
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.1 h) hq0
    · exact h
  have hdvd : T ∣ H.relIndex K := by
    rw [← hord, AddSubgroup.relIndex, AddSubgroup.index_eq_card]
    exact addOrderOf_dvd_natCard _
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd

theorem sq_le_relIndex {G : Type*} [AddCommGroup G] (A B C : AddSubgroup G) (T : ℕ) (hT : T.Prime)
    (h0 : A.relIndex B ≠ 0) (hAC : A ⊓ B ≤ C) (hCB : C ≤ B) (h1 : ∃ k ∈ B, k ∉ C)
    (h2 : ∃ k ∈ C, k ∉ A) (hkill : ∀ k ∈ B, T • k ∈ A) :
    T ^ 2 ≤ A.relIndex B := by
  have hmid : (A ⊓ B).relIndex C = A.relIndex C := by
    rw [← AddSubgroup.inf_relIndex_right (A ⊓ B) C, ← AddSubgroup.inf_relIndex_right A C,
      inf_assoc, inf_eq_right.2 hCB]
  have hAB : A.relIndex B = A.relIndex C * C.relIndex B := by
    rw [← AddSubgroup.inf_relIndex_right A B, ← AddSubgroup.relIndex_mul_relIndex _ _ _ hAC hCB, hmid]
  have hAC0 : A.relIndex C ≠ 0 := by
    intro h; apply h0; rw [hAB, h, zero_mul]
  have hCB0 : C.relIndex B ≠ 0 := by
    intro h; apply h0; rw [hAB, h, mul_zero]
  have hle1 : T ≤ A.relIndex C := prime_le_relIndex A C T hT hAC0 h2 (fun k hk => hkill k (hCB hk))
  have hle2 : T ≤ C.relIndex B := prime_le_relIndex C B T hT hCB0 h1
    (fun k hk => hAC (AddSubgroup.mem_inf.2 ⟨hkill k hk, B.nsmul_mem hk T⟩))
  rw [hAB, sq]
  exact Nat.mul_le_mul hle1 hle2

theorem nsmul_mem_loc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (L M : Submodule (𝓞 E) (Fin n → E)) (T : ℕ)
    (h : ∀ x ∈ M, T • x ∈ L) : ∀ y ∈ loc v M, T • y ∈ loc v L := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨T • m, h m hm, ?_⟩
    funext i
    simp
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [smul_add]; exact Submodule.add_mem _ hx hz
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx

theorem nsmul_mem_of_dual {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (T : ℕ)
    (h : ∀ y ∈ dualSet (σ : E →+* E) J L, (T : E) • y ∈ L) : ∀ x ∈ dualL σ J L, T • x ∈ L := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => rw [← Nat.cast_smul_eq_nsmul E]; exact h y hy
  | zero => rw [smul_zero]; exact L.zero_mem
  | add x z _ _ hx hz => rw [smul_add]; exact L.add_mem hx hz
  | smul a x _ hx => rw [smul_comm]; exact L.smul_mem a hx

theorem sq_le_local_index : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → ∀ (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ((∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = (sp (y b)).1) ↔ (∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).2 = (sp (y b)).2)) → (loc v L).toAddSubgroup.relIndex (loc v (dualL cm.sig J L)).toAddSubgroup ≠ 0 → T ^ 2 ≤ (loc v L).toAddSubgroup.relIndex (loc v (dualL cm.sig J L)).toAddSubgroup := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f L hT hsplit hrank hTL v hv sp hsp h1 hiff h0
  classical
  obtain ⟨_, _, hkillT, _, hnt⟩ := hTL
  have hkill : ∀ k ∈ (loc v (dualL cm.sig J L)).toAddSubgroup, T • k ∈ (loc v L).toAddSubgroup :=
    fun k hk => nsmul_mem_loc v L (dualL cm.sig J L) T (nsmul_mem_of_dual cm.sig J L T hkillT) k hk
  obtain ⟨x, hxB, hxA⟩ := hnt v hv
  have hsc := split_components F E cm n J hJ hdet v sp hsp h1
  have hnot1 : ¬ (∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = (sp (y b)).1) := by
    intro hP1
    exact hxA ((hsc.1 L x).2 ⟨hP1 x hxB, hiff.1 hP1 x hxB⟩)
  have hnot2 : ¬ (∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).2 = (sp (y b)).2) :=
    fun hP2 => hnot1 (hiff.2 hP2)
  push Not at hnot1 hnot2
  obtain ⟨y1, hy1B, hy1⟩ := hnot1
  obtain ⟨y2, hy2B, hy2⟩ := hnot2
  have heV : sp.symm (0, 1) ∈ intV E v := by
    have hI := (split_integral_local F E v sp h1 (sp.symm (0, 1))).2
    rw [RingEquiv.apply_symm_apply] at hI
    exact hI ⟨zero_mem _, one_mem _⟩
  have hcomp : ∀ b, sp (((⟨sp.symm (0, 1), heV⟩ : intV E v) • y2) b) = (0, (sp (y2 b)).2) := by
    intro b
    show sp (sp.symm (0, 1) * y2 b) = _
    rw [map_mul, RingEquiv.apply_symm_apply]
    ext <;> simp
  let C : AddSubgroup (Fin n → E ⊗[F] v.adicCompletion F) :=
    { carrier := {y | y ∈ loc v (dualL cm.sig J L) ∧ ∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = (sp (y b)).1}
      add_mem' := by
        intro a c ha hc
        obtain ⟨ha, za, hza, hza'⟩ := ha
        obtain ⟨hc, zc, hzc, hzc'⟩ := hc
        refine ⟨Submodule.add_mem _ ha hc, za + zc, Submodule.add_mem _ hza hzc, fun b => ?_⟩
        simp only [Pi.add_apply, map_add (f := _), Prod.fst_add, hza', hzc']
      zero_mem' := by
        refine ⟨Submodule.zero_mem _, 0, Submodule.zero_mem _, fun b => rfl⟩
      neg_mem' := by
        intro a ha
        obtain ⟨ha, za, hza, hza'⟩ := ha
        refine ⟨Submodule.neg_mem _ ha, -za, Submodule.neg_mem _ hza, fun b => ?_⟩
        simp only [Pi.neg_apply, map_neg, Prod.fst_neg, hza'] }
  have hAC : (loc v L).toAddSubgroup ⊓ (loc v (dualL cm.sig J L)).toAddSubgroup ≤ C := by
    intro y hy
    obtain ⟨hyA, hyB⟩ := AddSubgroup.mem_inf.1 hy
    exact ⟨hyB, y, hyA, fun b => rfl⟩
  have hCB : C ≤ (loc v (dualL cm.sig J L)).toAddSubgroup := fun y hy => hy.1
  have hBC : ∃ k ∈ (loc v (dualL cm.sig J L)).toAddSubgroup, k ∉ C := by
    refine ⟨y1, hy1B, fun hC => ?_⟩
    obtain ⟨z, hz, hz'⟩ := hC.2
    obtain ⟨b, hb⟩ := hy1 z hz
    exact hb (hz' b)
  have hCA : ∃ k ∈ C, k ∉ (loc v L).toAddSubgroup := by
    refine ⟨(⟨sp.symm (0, 1), heV⟩ : intV E v) • y2,
      ⟨Submodule.smul_mem _ _ hy2B, 0, Submodule.zero_mem _, fun b => ?_⟩, fun hA => ?_⟩
    · rw [hcomp b]; simp
    · obtain ⟨b, hb⟩ := hy2 _ hA
      apply hb
      rw [hcomp b]
  exact sq_le_relIndex _ _ C T hT h0 hAC hCB hBC hCA hkill

end GlobalTheory.St.G.IdxLower
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimeSqLeLocalHermitianDualIndexStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.prime_sq_le_local_hermitian_dual_index : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → ∀ (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ((∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = (sp (y b)).1) ↔ (∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).2 = (sp (y b)).2)) → (loc v L).toAddSubgroup.relIndex (loc v (dualL cm.sig J L)).toAddSubgroup ≠ 0 → T ^ 2 ≤ (loc v L).toAddSubgroup.relIndex (loc v (dualL cm.sig J L)).toAddSubgroup := by
  first | exact @GlobalTheory.St.G.IdxLower.sq_le_local_index | exact GlobalTheory.St.G.IdxLower.sq_le_local_index | (intros; apply GlobalTheory.St.G.IdxLower.sq_le_local_index <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdLocalRelIndexDvdHermitianDual

section

@[expose] public section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.GlobIdx

theorem prod_relIndex_dvd {G ι : Type} [AddCommGroup G] {M : ι → Type} [∀ i, AddCommGroup (M i)]
    (B A : AddSubgroup G) (H K : ∀ i, AddSubgroup (M i)) (φ : ∀ i, G →+ M i) (S : Finset ι)
    (hA : ∀ i, ∀ x ∈ A, φ i x ∈ K i) (hB : ∀ i, ∀ x ∈ B, φ i x ∈ H i)
    (hs : ∀ y : ∀ i, M i, (∀ i, y i ∈ K i) → ∃ x ∈ A, ∀ i ∈ S, φ i x - y i ∈ H i) :
    ∏ i ∈ S, (H i).relIndex (K i) ∣ B.relIndex A := by
  classical
  let ψ : A →+ (∀ i : S, K i ⧸ (H i).addSubgroupOf (K i)) :=
    AddMonoidHom.pi fun i : S => (QuotientAddGroup.mk' ((H i).addSubgroupOf (K i))).comp
      (((φ i).comp A.subtype).codRestrict (K i) fun x => hA i x x.2)
  have hψ : Function.Surjective ψ := by
    intro q
    choose r hr using fun i : S => QuotientAddGroup.mk_surjective (q i)
    obtain ⟨x, hx, h⟩ := hs (fun i => if hi : i ∈ S then (r ⟨i, hi⟩ : M i) else 0) (fun i => by
      by_cases hi : i ∈ S
      · simp only [hi, dif_pos]; exact (r ⟨i, hi⟩).2
      · simp only [hi, dif_neg, not_false_eq_true]; exact zero_mem _)
    refine ⟨⟨x, hx⟩, funext fun i => ?_⟩
    rw [← hr i]
    have h1 := h i i.2
    simp only [i.2, dif_pos] at h1
    show (QuotientAddGroup.mk (⟨φ i x, hA i x hx⟩ : K i) : K i ⧸ (H i).addSubgroupOf (K i)) = _
    rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]
    exact h1
  have hker : B.addSubgroupOf A ≤ ψ.ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker]
    funext i
    show (QuotientAddGroup.mk (⟨φ i x, hA i x x.2⟩ : K i) : K i ⧸ (H i).addSubgroupOf (K i)) = 0
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    exact hB i x hx
  have h1 : ψ.ker.index ∣ B.relIndex A := AddSubgroup.index_dvd_of_le hker
  rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hψ, AddSubgroup.card_top, Nat.card_pi] at h1
  rw [← Finset.prod_coe_sort S]
  exact h1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem nsmul_mem_loc (v : HeightOneSpectrum (𝓞 F)) (T : ℕ) (L D : Submodule (𝓞 E) (Fin n → E))
    (h : ∀ y ∈ D, T • y ∈ L) : ∀ z ∈ loc v D, T • z ∈ loc v L := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    refine Submodule.subset_span ⟨T • y, h y hy, ?_⟩
    funext i
    simp only [Pi.smul_apply, map_nsmul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem prod_loc_relIndex_dvd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), (∀ v ∈ S, (T : 𝓞 F) ∈ v.asIdeal) → ∏ v ∈ S, (loc v L).toAddSubgroup.relIndex (loc v (dualL cm.sig J L)).toAddSubgroup ∣ L.toAddSubgroup.relIndex (dualL cm.sig J L).toAddSubgroup := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f L hT _ _ hL S _
  obtain ⟨hlat, -, hTL, -, -⟩ := hL
  have hfin := (GlobalTheory.St.G.dualL_local_adelic F E cm n J hJ hdet L hlat).1.1
  have hTD : ∀ y ∈ dualL cm.sig J L, T • y ∈ L := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => rw [← Nat.cast_smul_eq_nsmul E]; exact hTL x hx
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  refine prod_relIndex_dvd (M := fun v : HeightOneSpectrum (𝓞 F) => Fin n → E ⊗[F] v.adicCompletion F)
    L.toAddSubgroup (dualL cm.sig J L).toAddSubgroup (fun v => (loc v L).toAddSubgroup)
    (fun v => (loc v (dualL cm.sig J L)).toAddSubgroup)
    (fun v => AddMonoidHom.compLeft (inclE (F := F) (E := E) (v.adicCompletion F)).toAddMonoidHom (Fin n)) S
    (fun v x hx => Submodule.subset_span ⟨x, hx, rfl⟩) (fun v x hx => Submodule.subset_span ⟨x, hx, rfl⟩) ?_
  intro y hy
  obtain ⟨x, hx, h⟩ := GlobalTheory.OverCompare.exists_lattice_approx_all F E n (dualL cm.sig J L) hfin T hT.ne_zero y hy
  refine ⟨x, hx, fun v _ => ?_⟩
  obtain ⟨z, hz, e⟩ := h v
  have h1 := nsmul_mem_loc v T L _ hTD z hz
  have e2 : (fun i => inclE (F := F) (v.adicCompletion F) (x i)) - y v = -(T • z) := by
    rw [e]; abel
  show (fun i => inclE (F := F) (v.adicCompletion F) (x i)) - y v ∈ loc v L
  rw [e2]
  exact neg_mem h1

end GlobalTheory.St.G.GlobIdx
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdLocalRelIndexDvdHermitianDualStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.prod_local_relIndex_dvd_hermitian_dual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), (∀ v ∈ S, (T : 𝓞 F) ∈ v.asIdeal) → ∏ v ∈ S, (loc v L).toAddSubgroup.relIndex (loc v (dualL cm.sig J L)).toAddSubgroup ∣ L.toAddSubgroup.relIndex (dualL cm.sig J L).toAddSubgroup := by
  first | exact @GlobalTheory.St.G.GlobIdx.prod_loc_relIndex_dvd | exact GlobalTheory.St.G.GlobIdx.prod_loc_relIndex_dvd | (intros; apply GlobalTheory.St.G.GlobIdx.prod_loc_relIndex_dvd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLevelLocalDualQuotientLengthOne

section

@[expose] public section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem tidx_arith {ι : Type} (s : Finset ι) (r : ι → ℕ) (T f : ℕ) (hT : T.Prime) (hcard : s.card = f)
    (hdvd : ∏ i ∈ s, r i ∣ T ^ (2 * f)) (hlow : ∀ i ∈ s, r i ≠ 0 → T ^ 2 ≤ r i) : ∀ i ∈ s, r i = T ^ 2 := by
  have hT0 : 0 < T := hT.pos
  have hpow0 : T ^ (2 * f) ≠ 0 := pow_ne_zero _ hT.ne_zero

  have hprod0 : ∏ i ∈ s, r i ≠ 0 := by
    intro h
    rw [h] at hdvd
    exact hpow0 (zero_dvd_iff.mp hdvd)
  have hge : ∀ i ∈ s, T ^ 2 ≤ r i := fun i hi =>
    hlow i hi (fun h => hprod0 (Finset.prod_eq_zero hi h))

  have hle : ∏ i ∈ s, r i ≤ ∏ _i ∈ s, T ^ 2 := by
    rw [Finset.prod_const, hcard, ← pow_mul]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hpow0) hdvd
  intro i hi
  by_contra hne
  have hlt : ∏ _i ∈ s, T ^ 2 < ∏ i ∈ s, r i :=
    Finset.prod_lt_prod₀ (fun j _ => pow_pos hT0 2) hge ⟨i, hi, lt_of_le_of_ne (hge i hi) (Ne.symm hne)⟩
  exact absurd hle (not_le.mpr hlt)

theorem tLat_local_index : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → (loc v L).toAddSubgroup.relIndex (loc v (dualL cm.sig J L)).toAddSubgroup = T ^ 2 ∧ ∃ d ∈ loc v (dualL cm.sig J L), ∀ x ∈ loc v (dualL cm.sig J L), ∃ a ∈ intV E v, x - a • d ∈ loc v L := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f L hT hs hdeg hL v hv
  obtain ⟨hncard, hloc⟩ := GlobalTheory.St.G.SplitPrime.split_place F E cm T hT hs

  have hF : Module.finrank ℚ F = f := by
    have h := Module.finrank_mul_finrank ℚ F E
    rw [cm.deg2, hdeg] at h
    omega
  have hfin : {w : HeightOneSpectrum (𝓞 F) | (T : 𝓞 F) ∈ w.asIdeal}.Finite :=
    Set.finite_of_ncard_pos (by rw [hncard]; exact Module.finrank_pos)
  have hcard : hfin.toFinset.card = f := by
    rw [← Set.ncard_eq_toFinset_card _ hfin, hncard, hF]

  have hlow : ∀ w ∈ hfin.toFinset,
      (loc w L).toAddSubgroup.relIndex (loc w (dualL cm.sig J L)).toAddSubgroup ≠ 0 →
      T ^ 2 ≤ (loc w L).toAddSubgroup.relIndex (loc w (dualL cm.sig J L)).toAddSubgroup := by
    intro w hw h0
    have hw' : (T : 𝓞 F) ∈ w.asIdeal := (Set.Finite.mem_toFinset hfin).mp hw
    obtain ⟨_, _, sp, hsp1, hsp2⟩ := hloc w hw'
    exact GlobalTheory.T.prime_sq_le_local_hermitian_dual_index F E cm n J hJ hdet T f L hT hs hdeg hL w hw' sp hsp1 hsp2
      (GlobalTheory.T.split_place_dual_quotient_components_iff F E cm n J hJ hdet T f L hT hs hdeg hL w hw' sp hsp1 hsp2) h0

  have hdvd := GlobalTheory.T.prod_local_relIndex_dvd_hermitian_dual F E cm n J hJ hdet T f L hT hs hdeg hL hfin.toFinset
    (fun w hw => (Set.Finite.mem_toFinset hfin).mp hw)
  rw [hL.2.2.2.1] at hdvd
  have heq := tidx_arith hfin.toFinset
    (fun w => (loc w L).toAddSubgroup.relIndex (loc w (dualL cm.sig J L)).toAddSubgroup)
    T f hT hcard hdvd hlow v ((Set.Finite.mem_toFinset hfin).mpr hv)
  refine ⟨heq, ?_⟩
  obtain ⟨_, _, sp, hsp1, hsp2⟩ := hloc v hv
  exact GlobalTheory.T.local_hermitian_dual_quotient_cyclic_split_place F E cm n J hJ hdet T f L hT hs hdeg hL v hv sp hsp1 hsp2
    (GlobalTheory.T.split_place_dual_quotient_components_iff F E cm n J hJ hdet T f L hT hs hdeg hL v hv sp hsp1 hsp2) heq

end GlobalTheory.St.G
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLevelLocalDualQuotientLengthOneStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.hermitianLattice_level_local_dual_quotient_length_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → (loc v L).toAddSubgroup.relIndex (loc v (dualL cm.sig J L)).toAddSubgroup = T ^ 2 ∧ ∃ d ∈ loc v (dualL cm.sig J L), ∀ x ∈ loc v (dualL cm.sig J L), ∃ a ∈ intV E v, x - a • d ∈ loc v L := by
  first | exact @GlobalTheory.St.G.tLat_local_index | exact GlobalTheory.St.G.tLat_local_index | (intros; apply GlobalTheory.St.G.tLat_local_index <;> assumption)
end
end
