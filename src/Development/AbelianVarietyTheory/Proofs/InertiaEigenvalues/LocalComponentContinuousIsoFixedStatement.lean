module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicPartSpannedBySplitPlaceLocalComponentStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalIrreducibleFixedVectors
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEigenFamily

section

@[expose] public section

namespace GlobalTheory.EigenFamilyStabilizer

def stab {G V ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (θ : G → ℂ)
    (h1 : θ 1 = 1) (hm : ∀ a ∈ K, ∀ b ∈ K, θ (a * b) = θ a * θ b) (y : ι → V) : Subgroup K where
  carrier := {k | θ k = 1 ∧ ∀ i, ρ k (y i) = y i}
  one_mem' := ⟨by simpa using h1, fun i => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, fun i => ?_⟩
    · rw [Subgroup.coe_mul, hm _ a.2 _ b.2, ha, hb, one_mul]
    · rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb', ha']
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨?_, fun i => ?_⟩
    · have := hm _ (a⁻¹).2 _ a.2
      rw [ha, mul_one, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, h1] at this
      exact this.symm
    · conv_lhs => rw [← ha' i]
      rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.coe_mul, inv_mul_cancel]
      simp

theorem exists_eigen_family : ∀ {G V W ι : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : AddCommGroup V] [inst_4 : Module ℂ V] [inst_5 : AddCommGroup W] [inst_6 : Module ℂ W] [inst_7 : Fintype ι] {ρ : Representation ℂ G V}, GlobalTheory.PRep.IsSmooth ρ → ∀ {K : Subgroup G}, IsCompact (↑K : Set G) → ∀ {U : Set G}, IsOpen U → (1 : G) ∈ U → ∀ (θ : G → ℂ), (∀ g ∈ U, g ∈ K → θ g = (1 : ℂ)) → (∀ a ∈ K, ∀ b ∈ K, θ (a * b) = θ a * θ b) → ∀ (T : ι → V →ₗ[ℂ] W) (y : ι → V), (∀ k ∈ K, ∑ i : ι, (T i : V → W) (((ρ : G → V →ₗ[ℂ] V) k : V → V) (y i)) = θ k • ∑ i : ι, (T i : V → W) (y i)) → ∃ (u : ι → V), (∀ (j : ι), ∀ h ∈ K, ((ρ : G → V →ₗ[ℂ] V) h : V → V) (u j) = θ h • u j) ∧ ∑ i : ι, (T i : V → W) (u i) = ∑ i : ι, (T i : V → W) (y i) := by
  intro G V W ι _ _ _ _ _ _ _ _ ρ hρ K hK U hU hU1 θ hθ hm T y hy
  classical
  have h1 : θ 1 = 1 := hθ 1 hU1 K.one_mem
  let H : Subgroup K := stab ρ K θ h1 hm y
  have hHo : IsOpen (H : Set K) := by
    apply Subgroup.isOpen_of_mem_nhds H (g := 1)
    have ho : IsOpen (U ∩ ⋂ i, {g : G | ρ g (y i) = y i}) :=
      hU.inter (isOpen_iInter_of_finite fun i => hρ (y i))
    have ho' : IsOpen ((Subtype.val : K → G) ⁻¹' (U ∩ ⋂ i, {g : G | ρ g (y i) = y i})) :=
      ho.preimage continuous_subtype_val
    refine Filter.mem_of_superset (ho'.mem_nhds ?_) ?_
    · refine ⟨hU1, Set.mem_iInter.2 fun i => ?_⟩
      simp
    · rintro k ⟨hk, hk'⟩
      exact ⟨hθ _ hk k.2, fun i => Set.mem_iInter.1 hk' i⟩
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : Finite (K ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHo
  letI : Fintype (K ⧸ H) := Fintype.ofFinite _
  let f : ι → K → V := fun j k => θ (k⁻¹ : K) • ρ k (y j)
  have hf : ∀ j (k : K) (s : K), s ∈ H → f j (k * s) = f j k := by
    intro j k s hs
    have hs' : θ (s⁻¹ : K) = 1 := (H.inv_mem hs).1
    simp only [f]
    rw [mul_inv_rev, Subgroup.coe_mul, hm _ (s⁻¹).2 _ (k⁻¹).2, hs', one_mul, Subgroup.coe_mul, map_mul,
      Module.End.mul_apply, hs.2 j]
  let F : ι → K ⧸ H → V := fun j q => f j q.out
  have hF : ∀ j (k : K), F j (k : K ⧸ H) = f j k := by
    intro j k
    obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul H k
    simp only [F]
    rw [hs, hf j k s s.2]
  have hact : ∀ j (h : K) (q : K ⧸ H), ρ h (F j q) = θ h • F j (h • q) := by
    intro j h q
    induction q using QuotientGroup.induction_on with
    | H k =>
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, hF, hF]
      simp only [f]
      rw [map_smul, smul_smul, mul_comm (θ h), ← hm _ ((h * k)⁻¹).2 _ h.2, ← Subgroup.coe_mul,
        Subgroup.coe_mul K h k, map_mul, Module.End.mul_apply]
      congr 3
      group
  have hN : (Fintype.card (K ⧸ H) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨fun j => (Fintype.card (K ⧸ H) : ℂ)⁻¹ • ∑ q, F j q, fun j h hh => ?_, ?_⟩

  · rw [map_smul, map_sum, smul_comm]
    apply congrArg ((Fintype.card (K ⧸ H) : ℂ)⁻¹ • ·)
    rw [Finset.sum_congr rfl fun q _ => hact j ⟨h, hh⟩ q, ← Finset.smul_sum]
    exact congrArg (θ h • ·) (Equiv.sum_comp (MulAction.toPerm (⟨h, hh⟩ : K)) (F j))
  · have hq : ∀ q, ∑ i, T i (F i q) = ∑ i, T i (y i) := by
      intro q
      simp only [F, f, map_smul]
      rw [← Finset.smul_sum, hy _ q.out.2, smul_smul, ← hm _ (q.out⁻¹).2 _ q.out.2, ← Subgroup.coe_mul,
        inv_mul_cancel, Subgroup.coe_one, h1, one_smul]

    simp only [map_smul, map_sum, Finset.sum_apply]
    rw [← Finset.smul_sum, Finset.sum_comm, Finset.sum_congr rfl fun q _ => hq q, Finset.sum_const,
      Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN, one_smul]

end GlobalTheory.EigenFamilyStabilizer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentContinuousIsoFixed

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EigLocalSum

open GlobalTheory.PRep

theorem exists_eigen_family {G V W ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [Fintype ι]
    {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {K : Subgroup G} (hK : IsCompact (K : Set G))
    {U : Set G} (hU : IsOpen U) (h1 : (1 : G) ∈ U) (θ : G → ℂ) (hθU : ∀ g ∈ U, g ∈ K → θ g = 1)
    (hmul : ∀ a ∈ K, ∀ b ∈ K, θ (a * b) = θ a * θ b)
    (T : ι → V →ₗ[ℂ] W) (y : ι → V)
    (hinv : ∀ k ∈ K, ∑ i, T i (ρ k (y i)) = θ k • ∑ i, T i (y i)) :
    ∃ u : ι → V, (∀ j, ∀ h ∈ K, ρ h (u j) = θ h • u j) ∧ ∑ i, T i (u i) = ∑ i, T i (y i) := by
  first
  | exact @_root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family
  | exact _root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family
  | (apply _root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family <;> assumption)
  | (intros; apply _root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family ..)



theorem exists_eigen_local_sum : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (K : Subgroup (GL (Fin n) (s.w.adicCompletion L))) (θ : GL (Fin n) (s.w.adicCompletion L) → ℂ) (U : Set (GL (Fin n) (s.w.adicCompletion L))), K ≤ GlobalTheory.SplitWeil.KO (s.w.adicCompletion L) (Fin n) → GlobalTheory.SplitWeil.KOne (s.w.adicCompletion L) (Fin n) ≤ K → IsOpen U → (1 : GL (Fin n) (s.w.adicCompletion L)) ∈ U → (∀ g ∈ U, g ∈ K → θ g = 1) → ∀ f ∈ NG.isoTyp a.ρ S, (∀ x : GAf L n, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) ∈ K → NG.rt L n x f = θ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) • f) → ∀ (ι : Type) [Fintype ι] (xs : ι → GAf L n) (z : ι → ℂ), (∀ j, TrivOutside {s.v} (xs j)) → ∑ j, z j • NG.rt L n (xs j) f ≠ 0 → ∃ y : σ.V, (∀ h ∈ K, σ.ρ h y = θ h • y) ∧ ∑ j, z j • σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (xs j))) y ≠ 0 := by
  intro L _ _ _ n a S hS s σ hloc c hc hci K θ U hK hKOne hU hU1 hθU f hf hθ ι _ xs z hxs hz
  classical
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hz
    simp
  have hrt : ∀ h ∈ K, ∃ x : GAf L n, TrivOutside {s.v} x ∧
      Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) = h ∧ NG.rt L n x f = θ h • f := by
    intro h hh
    obtain ⟨x, hx, e⟩ := GlobalTheory.EigLocal.exists_trivOutside_map_loc n s c h
    exact ⟨x, hx, e, by rw [hθ x hx (e ▸ hh), e]⟩
  have hmul : ∀ k ∈ K, ∀ k' ∈ K, θ (k * k') = θ k * θ k' := by
    intro k hk k' hk'
    obtain ⟨x, hx, e, hfx⟩ := hrt k hk
    obtain ⟨x', hx', e', hfx'⟩ := hrt k' hk'
    have hxx : TrivOutside {s.v} (x * x') := GlobalTheory.SatInd.CosetFin.trivOutside_mul hx hx'
    have e2 : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (x * x')) = k * k' := by
      rw [map_mul, map_mul, e, e']
    have h2 := hθ (x * x') hxx (e2 ▸ mul_mem hk hk')
    rw [e2] at h2
    have h3 : NG.rt L n (x * x') f = NG.rt L n x (NG.rt L n x' f) := by
      funext g; simp [NG.rt, mul_assoc]
    rw [h3, hfx', map_smul, hfx, smul_smul] at h2
    have h4 : (θ (k * k') - θ k' * θ k) • f = 0 := by
      rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.1 h4 with h5 | h5
    · rw [sub_eq_zero.1 h5, mul_comm]
    · exact absurd h5 hf0
  have hmem := GlobalTheory.T.isotypicPart_spanned_by_splitPlace_localComponent L n a S hS s σ hloc c hc hci hf
  rw [iSup_subtype'] at hmem
  obtain ⟨F, hF, hFsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hmem
  choose y hy using fun i => LinearMap.mem_range.1 (hF i)
  have hsum : ∑ j : F.support, (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W)) (y j.1) = f := by
    rw [← hFsum, Finsupp.sum, ← Finset.sum_attach F.support]
    exact Finset.sum_congr rfl fun j _ => hy j.1
  have hKo : IsOpen (K : Set (GL (Fin n) (s.w.adicCompletion L))) :=
    Subgroup.isOpen_mono hKOne GlobalTheory.StepData.isOpen_KOne
  have hKc : IsCompact (K : Set (GL (Fin n) (s.w.adicCompletion L))) :=
    GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (K.isClosed_of_isOpen hKo) hK
  have hint : ∀ (j : F.support) (x : GAf L n), TrivOutside {s.v} x → ∀ v,
      (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W))
        (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) =
      NG.rt L n x ((j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W)) v) := fun j x hx v => j.1.2.2 x hx v
  obtain ⟨u, hu, hus⟩ := exists_eigen_family σ.smooth hKc hU hU1 θ hθU hmul
    (fun j : F.support => (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W))) (fun j => y j.1) (by
      intro k hk
      obtain ⟨x, hx, e, hfx⟩ := hrt k hk
      subst e

      rw [Finset.sum_congr rfl fun j _ => hint j x hx (y j.1), ← map_sum, hsum, hfx])
  rw [hsum] at hus
  by_contra hall
  push_neg at hall
  apply hz
  have key : ∀ j, ∑ m, z m • σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (xs m))) (u j) = 0 := by
    intro j
    by_contra hne
    exact hne (hall (u j) (hu j))
  calc ∑ m, z m • NG.rt L n (xs m) f
      = ∑ m, z m • ∑ j : F.support, (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W))
          (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (xs m))) (u j)) := by
        refine Finset.sum_congr rfl fun m _ => ?_

        rw [← hus, map_sum]
        congr 1
        exact Finset.sum_congr rfl fun j _ => (hint j (xs m) (hxs m) (u j)).symm
    _ = ∑ j : F.support, (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W))
          (∑ m, z m • σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (xs m))) (u j)) := by

        simp only [map_sum, map_smul, Finset.smul_sum]
        exact Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero fun j _ => by rw [key j, map_zero]

end GlobalTheory.EigLocalSum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentContinuousIsoFixedStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.local_component_continuous_iso_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (K : Subgroup (GL (Fin n) (s.w.adicCompletion L))) (θ : GL (Fin n) (s.w.adicCompletion L) → ℂ) (U : Set (GL (Fin n) (s.w.adicCompletion L))), K ≤ GlobalTheory.SplitWeil.KO (s.w.adicCompletion L) (Fin n) → GlobalTheory.SplitWeil.KOne (s.w.adicCompletion L) (Fin n) ≤ K → IsOpen U → (1 : GL (Fin n) (s.w.adicCompletion L)) ∈ U → (∀ g ∈ U, g ∈ K → θ g = 1) → ∀ f ∈ NG.isoTyp a.ρ S, (∀ x : GAf L n, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) ∈ K → NG.rt L n x f = θ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) • f) → ∀ (ι : Type) [Fintype ι] (xs : ι → GAf L n) (z : ι → ℂ), (∀ j, TrivOutside {s.v} (xs j)) → ∑ j, z j • NG.rt L n (xs j) f ≠ 0 → ∃ y : σ.V, (∀ h ∈ K, σ.ρ h y = θ h • y) ∧ ∑ j, z j • σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (xs j))) y ≠ 0 := by
  first | exact @GlobalTheory.EigLocalSum.exists_eigen_local_sum | exact GlobalTheory.EigLocalSum.exists_eigen_local_sum | (intros; apply GlobalTheory.EigLocalSum.exists_eigen_local_sum <;> assumption)
end
end
