module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPartnerSplittingSelfDualLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicHermitianSpaceOfNegativeIndexStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeOfEqSpanFracSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeComapSubspaceRingOfIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryPosDefHermitianSameRank
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFromBlocks
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualOrthogonalComplementHyperbolicPlan

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaneCompl

theorem gram_sum {D : D7} (S : HSp D) (a b : Fin S.rank → D.host.E) :
    ∑ i, ∑ j, star (a i) * S.gram i j * b j = S.hT (S.frame.equivFun.symm a) (S.frame.equivFun.symm b) := by

  simp only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
  LinearMap.smul_apply, smul_eq_mul, Formalism.BasicNotions.HSpace.gram, starRingEnd_apply]
  simp only [Finset.mul_sum, RingHom.id_apply]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem exists_compl : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (x y : S.V)
    (s : (D.host.E →+* ℂ) → ℕ × ℕ), IsSelfDualC S Λ → S.hT x x = 0 → S.hT y y = 0 → S.hT x y = 1 →
    (∀ z, GlobalTheory.SqStepK.InLat S Λ z → GlobalTheory.SqStepK.InLat S Λ (S.hT y z • x) ∧ GlobalTheory.SqStepK.InLat S Λ (S.hT x z • y)) →
    ∃ (S₁ : HSp D) (Λ₁ : Submodule (𝓞 D.host.E) (Fin S₁.rank → D.host.E)) (ι : S₁.V →ₗ[D.host.E] S.V),
      GlobalTheory.SqStepK.PlaneSplit S S₁ Λ Λ₁ ι x y ∧ IsSelfDualC S₁ Λ₁ ∧ S₁.sig = s := by
  intro D S Λ x y s hΛ hxx hyy hxy hsplit
  have hyx : S.hT y x = 1 := by rw [← S.herm.eq x y, hxy, map_one]
  let W : Submodule D.host.E S.V := LinearMap.ker (LinearMap.pi fun j : Fin 2 => S.hT (![x, y] j))
  have hW : ∀ w, w ∈ W ↔ S.hT x w = 0 ∧ S.hT y w = 0 := by
    intro w
    simp only [W, LinearMap.mem_ker, funext_iff, LinearMap.pi_apply, Fin.forall_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Pi.zero_apply, Matrix.head_cons]
  have hdec : ∀ z, z - S.hT y z • x - S.hT x z • y ∈ W := by
    intro z
    rw [hW]
    constructor <;> simp [map_sub, hxx, hyy, hxy, hyx]
  have hind : LinearIndependent D.host.E ![x, y] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 := congrArg (S.hT x) hab
    have h2 := congrArg (S.hT y) hab
    simp [hxx, hyy, hxy, hyx] at h1 h2
    exact ⟨h2, h1⟩
  have hrk : 2 + Module.finrank D.host.E W = S.rank := by
    have := GlobalTheory.WittLow.finrank_orth S.herm S.nondeg ![x, y] hind
    rw [S.rank_eq] at this
    exact this

  have hrad : ∀ v : W, (∀ w : W, S.hT w v = 0) → v = 0 := by
    intro v hv
    have hv' := (hW v).1 v.2
    apply Subtype.ext
    apply S.nondeg.2 (v : S.V)
    intro z
    have e : z = S.hT y z • x + (z - S.hT y z • x - S.hT x z • y) + S.hT x z • y := by abel
    have h0 := hv ⟨_, hdec z⟩
    rw [e, map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ,
      LinearMap.smul_apply, LinearMap.smul_apply, hv'.1, hv'.2, h0]
    simp
  let h' : W →ₗ⋆[D.host.E] W →ₗ[D.host.E] D.host.E := S.hT.domRestrict₁₂ W W
  have hs' : h'.IsSymm := ⟨fun a b => S.herm.eq _ _⟩
  have hnd' : h'.Nondegenerate := ⟨fun a ha => hrad a fun b => by
    rw [← S.herm.eq]; exact (congrArg _ (ha b)).trans (map_zero _), fun a ha => hrad a ha⟩
  let Λ' : Submodule (𝓞 D.host.E) S.V := Λ.comap ((S.frame.equivFun : S.V →ₗ[D.host.E] (Fin S.rank → D.host.E)).restrictScalars (𝓞 D.host.E))
  have hΛ'm : ∀ z, z ∈ Λ' ↔ GlobalTheory.SqStepK.InLat S Λ z := fun z => Iff.rfl
  have hΛ'lat : Submodule.IsLattice D.host.E Λ' := GlobalTheory.ColRows.isLattice_comap_equiv S.frame.equivFun Λ hΛ.1
  have hΛ'd : ∀ z, z ∈ Λ' ↔ ∀ w ∈ Λ', ∃ b : 𝓞 D.host.E, (b : D.host.E) = S.hT w z := by
    intro z
    rw [hΛ'm, GlobalTheory.SqStepK.InLat, hΛ.2]
    constructor
    · intro h w hw
      obtain ⟨b, hb⟩ := h _ hw
      exact ⟨b, by rw [hb, gram_sum]; simp⟩
    · intro h a ha
      obtain ⟨b, hb⟩ := h (S.frame.equivFun.symm a) (by rw [hΛ'm, GlobalTheory.SqStepK.InLat, LinearEquiv.apply_symm_apply]; exact ha)
      exact ⟨b, by rw [hb, gram_sum]; simp⟩
  let L0 : Submodule (𝓞 D.host.E) W := Λ'.comap (W.subtype.restrictScalars (𝓞 D.host.E))
  have hL0m : ∀ u : W, u ∈ L0 ↔ (u : S.V) ∈ Λ' := fun u => Iff.rfl
  have hL0lat : Submodule.IsLattice D.host.E L0 := GlobalTheory.isLattice_comap_subtype_ringOfIntegers Λ' hΛ'lat W
  have hwz : ∀ z, z ∈ Λ' → z - S.hT y z • x - S.hT x z • y ∈ Λ' := by
    intro z hz
    obtain ⟨hs1, hr1⟩ := hsplit z ((hΛ'm z).1 hz)
    rw [hΛ'm, GlobalTheory.SqStepK.InLat, map_sub, map_sub]
    exact Λ.sub_mem (Λ.sub_mem hz hs1) hr1
  have hL0d : ∀ u : W, u ∈ L0 ↔ ∀ u' ∈ L0, ∃ b : 𝓞 D.host.E, (b : D.host.E) = S.hT u' u := by
    intro u
    have hu := (hW u).1 u.2
    rw [hL0m, hΛ'd]
    constructor
    · intro h u' hu'
      exact h _ hu'
    · intro h z hz
      obtain ⟨b, hb⟩ := h ⟨_, hdec z⟩ (hwz z hz)
      refine ⟨b, ?_⟩
      rw [hb]
      simp [map_sub, hu.1, hu.2]
  have hun : Formalism.HermitianLatticesTheory.IsUnimodular h' L0 := by
    ext v
    rw [GlobalTheory.WittLow.mem_dual, hL0d]
    refine forall₂_congr fun u' _ => ?_
    rw [Submodule.mem_one]
    rfl

  let S₁ : HSp D :=
    { V := W, hT := h', herm := hs', nondeg := hnd', rank := Module.finrank D.host.E W, rank_eq := rfl,
      frame := Module.finBasis D.host.E W, sig := s, L0 := L0, standardTuple_isLattice := hL0lat, baseLattice_isUnimodular := hun }
  let e₁ : (Fin (Module.finrank D.host.E W) → D.host.E) ≃ₗ[D.host.E] W := (Module.finBasis D.host.E W).equivFun.symm
  let Λ₁ : Submodule (𝓞 D.host.E) (Fin S₁.rank → D.host.E) :=
    L0.comap ((e₁ : (Fin (Module.finrank D.host.E W) → D.host.E) →ₗ[D.host.E] W).restrictScalars (𝓞 D.host.E))
  have hΛ₁m : ∀ v, v ∈ Λ₁ ↔ e₁ v ∈ L0 := fun v => Iff.rfl
  have hΛ₁lat : Submodule.IsLattice D.host.E Λ₁ := GlobalTheory.ColRows.isLattice_comap_equiv e₁ L0 hL0lat
  have hin : ∀ u : W, GlobalTheory.SqStepK.InLat S₁ Λ₁ u ↔ GlobalTheory.SqStepK.InLat S Λ (W.subtype u) := by
    intro u
    change (Module.finBasis D.host.E W).equivFun u ∈ Λ₁ ↔ _
    rw [hΛ₁m]
    change (Module.finBasis D.host.E W).equivFun.symm ((Module.finBasis D.host.E W).equivFun u) ∈ L0 ↔ _
    rw [LinearEquiv.symm_apply_apply, hL0m, hΛ'm]
    rfl
  refine ⟨S₁, Λ₁, W.subtype, ⟨?_, fun _ _ => rfl, hxx, hyy, hyx, fun u => ⟨((hW u).1 u.2).1, ((hW u).1 u.2).2⟩, hin, ?_⟩, ⟨hΛ₁lat, ?_⟩, rfl⟩
  · change S.rank = Module.finrank D.host.E W + 2
    omega
  · intro z hz
    obtain ⟨hs1, hr1⟩ := hsplit z hz
    refine ⟨S.hT y z, S.hT x z, ⟨_, hdec z⟩, hs1, hr1, (hin _).2 (hwz z hz), ?_⟩
    change z = S.hT y z • x + (z - S.hT y z • x - S.hT x z • y) + S.hT x z • y
    abel
  · intro v
    simp only [gram_sum]
    rw [hΛ₁m, hL0d]
    constructor
    · intro h a ha
      exact h _ ha
    · intro h u' hu'
      have := h (e₁.symm u') (by rw [hΛ₁m, LinearEquiv.apply_symm_apply]; exact hu')
      obtain ⟨b, hb⟩ := this
      refine ⟨b, ?_⟩
      rw [hb]
      change S.hT (e₁ (e₁.symm u') : S.V) _ = _
      rw [LinearEquiv.apply_symm_apply]
      rfl

end GlobalTheory.PlaneCompl
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualOrthogonalComplementHyperbolicPlanStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_selfDual_orthogonalComplement_hyperbolicPlane : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (x y : S.V)
    (s : (D.host.E →+* ℂ) → ℕ × ℕ), IsSelfDualC S Λ → S.hT x x = 0 → S.hT y y = 0 → S.hT x y = 1 →
    (∀ z, GlobalTheory.SqStepK.InLat S Λ z → GlobalTheory.SqStepK.InLat S Λ (S.hT y z • x) ∧ GlobalTheory.SqStepK.InLat S Λ (S.hT x z • y)) →
    ∃ (S₁ : HSp D) (Λ₁ : Submodule (𝓞 D.host.E) (Fin S₁.rank → D.host.E)) (ι : S₁.V →ₗ[D.host.E] S.V),
      GlobalTheory.SqStepK.PlaneSplit S S₁ Λ Λ₁ ι x y ∧ IsSelfDualC S₁ Λ₁ ∧ S₁.sig = s := by
  first | exact @GlobalTheory.PlaneCompl.exists_compl | exact GlobalTheory.PlaneCompl.exists_compl | (intros; apply GlobalTheory.PlaneCompl.exists_compl <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementNegativeIndexPred

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaneComplementSig

open Matrix

theorem hasSignature_plane : Formalism.UG.HasSignature (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := by
  refine GlobalTheory.FrameComplement.hasSignature_of_frame (by simp)
    (Matrix.of fun i k => Sum.elim (fun _ => ![1, 1 / 2] i) (fun _ => ![1, -1 / 2] i) k) ?_
  ext (a | a) (b | b) <;> fin_cases a <;> fin_cases b <;>
    simp [Formalism.UG.Jpq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, map_ofNat] <;> norm_num

theorem sig : ∀ (D : D7) (S S₁ : HSp D) (ι : S₁.V →ₗ[D.host.E] S.V) (x y : S.V) (q : ℕ), S.rank = S₁.rank + 2 →
    Formalism.BasicNotions.HSpace.IsIsomEmb S₁ S ι → S.hT x x = 0 → S.hT y y = 0 → S.hT x y = 1 →
    (∀ u, S.hT x (ι u) = 0 ∧ S.hT y (ι u) = 0) → NegIdx S (q + 1) →
    ∀ τ : D.host.E →+* ℂ, Formalism.UG.HasSignature (S₁.gram.map τ) (S₁.rank - q) q := by
  intro D S S₁ ι x y q hr hι hxx hyy hxy ho hneg τ
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ

  have hS : Formalism.UG.HasSignature (S.gram.map τ) (S.rank - (q + 1)) (q + 1) := by
    obtain ⟨ρ, hσ | hσ⟩ := GlobalTheory.DefiniteMult.exists_tauE_or_conj D τ
    · subst hσ
      simpa [gramAt] using hneg ρ
    · subst hσ
      have h1 := GlobalTheory.BottomIsom.hasSignature_map_star (by simpa [gramAt] using hneg ρ)
      rw [Matrix.map_map] at h1
      exact h1
  obtain ⟨⟨a, b⟩, h₁⟩ := GlobalTheory.WittLow.exists_sig S₁ τ
  have c₁ := (Formalism.UG.P.sig_data _ _ _ h₁).1
  have cS := (Formalism.UG.P.sig_data _ _ _ hS).1
  simp only [Fintype.card_fin] at c₁ cS
  let v : Fin S₁.rank ⊕ Fin 2 → S.V := Sum.elim (fun i => ι (S₁.frame i)) ![x, y]
  have hyx : S.hT y x = 1 := by
    have h := S.herm.eq x y
    rw [hxy, map_one] at h
    exact h.symm
  have hv : (Matrix.of fun k l => S.hT (v k) (v l)) =
      fromBlocks S₁.gram 0 0 (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) D.host.E) := by
    ext (i | i) (j | j)
    · simp only [v, Matrix.of_apply, fromBlocks_apply₁₁, Sum.elim_inl, HSpace.gram]; exact hι _ _
    · fin_cases j
      · have h := S.herm.eq x (ι (S₁.frame i))
        rw [(ho _).1, map_zero] at h
        simp [v, ← h]
      · have h := S.herm.eq y (ι (S₁.frame i))
        rw [(ho _).2, map_zero] at h
        simp [v, ← h]
    · fin_cases i
      · simpa [v] using (ho _).1
      · simpa [v] using (ho _).2
    · fin_cases i <;> fin_cases j <;> simp [v, hxx, hyy, hxy, hyx]
  have hF : Formalism.UG.HasSignature ((Matrix.of fun k l => S.hT (v k) (v l)).map τ) (a + 1) (b + 1) := by
    rw [hv, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero τ), Matrix.map_zero _ (map_zero τ)]
    have e : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) D.host.E).map τ = !![0, 1; 1, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [e]
    exact GlobalTheory.FrameComplement.hasSignature_fromBlocks h₁ hasSignature_plane
  have key := Formalism.BasicNotions.sig_family S τ hτ v hF hS
  have hb : b = q := by omega
  have ha : a = S₁.rank - q := by omega
  subst hb ha
  exact h₁

end GlobalTheory.PlaneComplementSig
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementNegativeIndexPredStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.hyperbolicPlaneComplement_negativeIndex_pred : ∀ (D : D7) (S S₁ : HSp D) (ι : S₁.V →ₗ[D.host.E] S.V) (x y : S.V) (q : ℕ), S.rank = S₁.rank + 2 →
    Formalism.BasicNotions.HSpace.IsIsomEmb S₁ S ι → S.hT x x = 0 → S.hT y y = 0 → S.hT x y = 1 →
    (∀ u, S.hT x (ι u) = 0 ∧ S.hT y (ι u) = 0) → NegIdx S (q + 1) →
    ∀ τ : D.host.E →+* ℂ, Formalism.UG.HasSignature (S₁.gram.map τ) (S₁.rank - q) q := by
  first | exact @GlobalTheory.PlaneComplementSig.sig | exact GlobalTheory.PlaneComplementSig.sig | (intros; apply GlobalTheory.PlaneComplementSig.sig <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneSplitSelfDualHermitianComplement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaneComplement

theorem plane_split_complement : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (q : ℕ),
    IsSelfDualC S Λ → NegIdx S (q + 1) → q + 2 ≤ S.rank → 3 ≤ S.rank →
    ∃ (S₁ : HSp D) (Λ₁ : Submodule (𝓞 D.host.E) (Fin S₁.rank → D.host.E)) (ι : S₁.V →ₗ[D.host.E] S.V) (x y : S.V),
      GlobalTheory.SqStepK.PlaneSplit S S₁ Λ Λ₁ ι x y ∧ S₁.SigOK ∧ IsSelfDualC S₁ Λ₁ ∧ NegIdx S₁ q := by
  intro D S Λ q hΛ hneg hq h3
  obtain ⟨x, hx0, hxx⟩ := GlobalTheory.T.exists_isotropic_hermitianSpace_of_negativeIndex D S (q + 1) hneg (by omega) (by omega) h3
  obtain ⟨y, hyy, hxy, hsp⟩ := GlobalTheory.T.exists_hyperbolicPartner_splitting_selfDualLattice D S Λ x hΛ hx0 hxx
  obtain ⟨S₁, Λ₁, ι, hPS, hSD, hs⟩ := GlobalTheory.T.exists_selfDual_orthogonalComplement_hyperbolicPlane D S Λ x y (fun _ => (S.rank - 2 - q, q)) hΛ hxx hyy hxy hsp
  have hrk : S.rank = S₁.rank + 2 := hPS.1
  have hsig := GlobalTheory.T.hyperbolicPlaneComplement_negativeIndex_pred D S S₁ ι x y q hrk hPS.2.1 hxx hyy hxy
    (fun u => ⟨(hPS.2.2.2.2.2.1 u).1, (hPS.2.2.2.2.2.1 u).2⟩) hneg
  have e : S.rank - 2 - q = S₁.rank - q := by omega
  refine ⟨S₁, Λ₁, ι, x, y, hPS, fun τ => ?_, hSD, fun τ => ?_⟩
  · rw [hs]; simp only [e]; exact hsig τ
  · exact hsig _

end GlobalTheory.PlaneComplement

end
end
end
