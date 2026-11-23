module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Finset.Defs
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
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Data.Finset.Image
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteRepsHalfStandardHomModNsmul
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemStdHom
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAnnihilatorOpenSubgroupInBox
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairFiniteAdeleZeroMulPairFiniteAdeleZero
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AddSubgroupFiniteQuotOfCommensurable

section

@[expose] public section

namespace GlobalTheory

theorem addSubgroup_finite_quot_of_commensurable : ∀ (V : Type) [AddCommGroup V] (A L : AddSubgroup V) (N M : ℕ), 0 < N → 0 < M → (∀ v : V, N • v = 0 → v = 0) → (∀ a ∈ A, N • a ∈ L) → (∀ l ∈ L, M • l ∈ A) → (∀ j : ℕ, 0 < j → ∃ R : Finset V, ∀ u ∈ L, ∃ r ∈ R, ∃ v ∈ L, u = r + j • v) → ∀ k : ℕ, 0 < k → ∃ R : Finset V, ∀ u ∈ A, ∃ r ∈ R, ∃ v ∈ A, u = r + k • v := by
  classical
  intro V _ A L N M hN hM htf hAL hLA hfin k hk
  obtain ⟨R₀, hR₀⟩ := hfin (k * N * M) (by positivity)
  let P : V → Prop := fun r₀ => ∃ a ∈ A, ∃ w ∈ L, N • a = r₀ + (k * N * M) • w
  let f : V → V := fun r₀ => if h : P r₀ then h.choose else 0
  refine ⟨R₀.image f, ?_⟩
  intro u hu
  obtain ⟨r₀, hr₀, v, hv, huv⟩ := hR₀ (N • u) (hAL u hu)
  have hP : P r₀ := ⟨u, hu, v, hv, huv⟩
  have hf : f r₀ = hP.choose := dif_pos hP
  obtain ⟨haA, w, hwL, haw⟩ := hP.choose_spec
  refine ⟨f r₀, Finset.mem_image_of_mem f hr₀, M • (v - w), hLA _ (L.sub_mem hv hwL), ?_⟩
  rw [hf]
  have key : N • (u - (hP.choose + k • M • (v - w))) = 0 := by
    have e : N • k • M • (v - w) = (k * N * M) • (v - w) := by
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rw [smul_sub, smul_add, huv, haw, e, smul_sub]
    abel
  exact sub_eq_zero.mp (htf _ key)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsIdemSumConjOfIsIdemSum

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

namespace GlobalTheory.IdemSumConj

theorem exists_isIdemSum_cA :
    ∀ (D : D7) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q →
      ∃ Q' : Finset (Formalism.L2.DIV.Pl D.host.E), IsIdemSum (cA D E₂) Q' := by
  intro D P e h
  classical
  refine ⟨P.image Formalism.L2.DIV.conjPl, ?_⟩
  obtain ⟨⟨es, hes, he⟩, hc⟩ := h
  refine ⟨⟨fun Q => cA D (es (Formalism.L2.DIV.conjPl Q)), ?_, ?_⟩, ?_⟩
  · intro Q hQ
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hQ
    show Formalism.L2.NTheta.IsIdemAt (cA D (es (Formalism.L2.DIV.conjPl (Formalism.L2.DIV.conjPl PP)))) (Formalism.L2.DIV.conjPl PP)
    rw [Formalism.L2.DIV.conjPl_conjPl]
    exact GlobalTheory.MovedIdem.isIdemAt_conj (hes PP hPP) fun x => Iff.rfl
  · rw [Finset.sum_image (fun a _ b _ (hab : Formalism.L2.DIV.conjPl a = Formalism.L2.DIV.conjPl b) => by
      rw [← Formalism.L2.DIV.conjPl_conjPl a, hab, Formalism.L2.DIV.conjPl_conjPl b])]
    simp only [Formalism.L2.DIV.conjPl_conjPl]

    rw [he, map_sum]
  · rw [GlobalTheory.MovedIdem.cA_cA, mul_comm]; exact hc

end GlobalTheory.IdemSumConj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsIdemSumConjOfIsIdemSumStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.exists_isIdemSum_conj_of_isIdemSum : ∀ (D : D7) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∃ Q' : Finset (Formalism.L2.DIV.Pl D.host.E), IsIdemSum (cA D E₂) Q' := by
  first | exact @GlobalTheory.IdemSumConj.exists_isIdemSum_cA | exact GlobalTheory.IdemSumConj.exists_isIdemSum_cA | (intros; apply GlobalTheory.IdemSumConj.exists_isIdemSum_cA <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulAnnihilatorHalfMemStandardHom

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

open scoped TensorProduct

noncomputable section



namespace GlobalTheory.HalfAnnStd

variable {D : D7}

theorem symplO_nsmul_swap (S T : HSp D) (N : ℕ) (x y : WO S T) :
    symplO S T (N • x) y = symplO S T x (N • y) := by
  have h := GlobalTheory.PlaceModel.symplO_smul S T (N : AE D) x y
  rwa [map_natCast, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul] at h

theorem exists_nsmul_frame_mem (S T : HSp D) : ∃ N : ℕ, 0 < N ∧
    ∀ y ∈ latO S T (GlobalTheory.PlaceModel.latFrame S : Set (Fin S.rank → D.host.E))
      (GlobalTheory.PlaceModel.latFrame T : Set (Fin T.rank → D.host.E)) (fun _ => True), N • y ∈ stdHom S T := by
  obtain ⟨M, hM, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame S).1.fg (GlobalTheory.PlaceModel.isSelfDualC_latFrame T).1.fg
  obtain ⟨K, hK, hKm⟩ := GlobalTheory.AdForm.exists_nsmul_mem_stdHom S T
  refine ⟨K * M, Nat.mul_pos hK hM, fun y hy => ?_⟩
  rw [mul_smul]
  refine hKm _ (Matrix.ext fun i j => ?_) fun i j => ?_
  · rw [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul, RingHom.map_mul, GlobalTheory.LatVac.infPart_of_mem hy i j,
      mul_zero, Matrix.zero_apply]
  · rw [Matrix.smul_apply, nsmul_eq_mul, RingHom.map_mul, map_natCast]
    exact hden y hy i j

theorem exists_nsmul_ann_mem_stdHom : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∃ N : ℕ, 0 < N ∧ ∀ u : WO S T, IsHalf (cA D E₂) u → (∀ x ∈ stdHom S T, IsHalf E₂ x → ψ (symplO S T x u) = 1) → N • u ∈ stdHom S T := by
  intro D ψ hψ S T Q e he
  obtain ⟨N, hN, hNm⟩ := exists_nsmul_frame_mem S T
  refine ⟨N * N, Nat.mul_pos hN hN, fun u hu hann => ?_⟩
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf := GlobalTheory.AnnihBox.infPart_cA' e (GlobalTheory.PlaceDatum.infPart_idemSum he)
  have hfix : cA D e • u = u := Matrix.ext fun i j => hu i j
  have hall : ∀ x ∈ stdHom S T, ψ (symplO S T x u) = 1 := fun x hx => by
    have h := hann (e • x) (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ e
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hee])) _ hx) fun i j => by
        change e * (e * _) = e * _
        rw [← mul_assoc, hee]
    rwa [GlobalTheory.PlaceModel.symplO_smul, hfix] at h
  rw [mul_smul]
  refine hNm _ (((GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame T)).1 _ (Matrix.ext fun i j => ?_)).2 fun y hy => ?_)
  · rw [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul, RingHom.map_mul, ← hu i j, RingHom.map_mul, hinf, zero_mul,
      mul_zero, Matrix.zero_apply]
  · rw [symplO_nsmul_swap, GlobalTheory.PlaceModel.symplO_skew, AddChar.map_neg_eq_inv, hall _ (hNm y hy), inv_one]

end GlobalTheory.HalfAnnStd

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulAnnihilatorHalfMemStandardHomStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.exists_nsmul_annihilator_half_mem_standardHom : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∃ N : ℕ, 0 < N ∧ ∀ u : WO S T, IsHalf (cA D E₂) u → (∀ x ∈ stdHom S T, IsHalf E₂ x → ψ (symplO S T x u) = 1) → N • u ∈ stdHom S T := by
  first | exact @GlobalTheory.HalfAnnStd.exists_nsmul_ann_mem_stdHom | exact GlobalTheory.HalfAnnStd.exists_nsmul_ann_mem_stdHom | (intros; apply GlobalTheory.HalfAnnStd.exists_nsmul_ann_mem_stdHom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteQuotientAnnihilatorStandardLatticeConjHalf

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

noncomputable section



namespace GlobalTheory.AnnConjHalf

variable {D : D7}

theorem symplO_add_right' (S T : HSp D) (x u v : WO S T) :
    symplO S T x (u + v) = symplO S T x u + symplO S T x v := by
  simp only [symplO, hO, Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem symplO_neg_right' (S T : HSp D) (x u : WO S T) :
    symplO S T x (-u) = -symplO S T x u := by
  simp only [symplO, hO, Matrix.neg_apply, map_neg, mul_neg, neg_mul, Finset.sum_neg_distrib]

theorem symplO_zero_right' (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  simp only [symplO, hO, Matrix.zero_apply, map_zero, mul_zero, zero_mul, Finset.sum_const_zero]

def annHalf (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (E₂ : AE D) : AddSubgroup (WO S T) where
  carrier := {u | IsHalf (cA D E₂) u ∧ ∀ x ∈ stdHom S T, IsHalf E₂ x → ψ (symplO S T x u) = 1}
  zero_mem' := ⟨fun i j => by simp, fun x _ _ => by rw [symplO_zero_right', AddChar.map_zero_eq_one]⟩
  add_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    refine ⟨fun i j => by rw [Matrix.add_apply, mul_add, hu i j, hv i j], fun x hx hxh => ?_⟩
    rw [symplO_add_right', AddChar.map_add_eq_mul, hu' x hx hxh, hv' x hx hxh, mul_one]
  neg_mem' := by
    rintro u ⟨hu, hu'⟩
    refine ⟨fun i j => by rw [Matrix.neg_apply, mul_neg, hu i j], fun x hx hxh => ?_⟩
    rw [symplO_neg_right', AddChar.map_neg_eq_inv, hu' x hx hxh, inv_one]

def stdHalf (S T : HSp D) (f : AE D) : AddSubgroup (WO S T) where
  carrier := {u | u ∈ stdHom S T ∧ IsHalf f u}
  zero_mem' := ⟨zero_mem _, fun i j => by simp⟩
  add_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    exact ⟨add_mem hu hv, fun i j => by rw [Matrix.add_apply, mul_add, hu' i j, hv' i j]⟩
  neg_mem' := by
    rintro u ⟨hu, hu'⟩
    exact ⟨neg_mem hu, fun i j => by rw [Matrix.neg_apply, mul_neg, hu' i j]⟩

theorem half_nsmul {m n : ℕ} {f : AE D} {u : Mx D m n} (hu : IsHalf f u) (N : ℕ) : IsHalf f (N • u) :=
  fun i j => by rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hu i j]

theorem nsmul_eq_zero_WO (S T : HSp D) {N : ℕ} (hN : 0 < N) (v : WO S T) (h : N • v = 0) : v = 0 := by
  ext i j
  have hij : N • v i j = 0 := by
    have := congrFun (congrFun h i) j
    rwa [Matrix.smul_apply] at this
  have hF : (N : D.host.F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hu : IsUnit ((N : ℕ) : AE D) := by
    have := (isUnit_iff_ne_zero.2 hF).map (algebraMap D.host.F (AE D))
    rwa [map_natCast] at this
  rw [nsmul_eq_mul] at hij
  rw [Matrix.zero_apply]
  exact (hu.mul_right_eq_zero).1 hij

theorem ann_conj_half_finite : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u : WO S T, IsHalf (cA D E₂) u → (∀ x ∈ stdHom S T, IsHalf E₂ x → ψ (symplO S T x u) = 1) → ∃ r ∈ R, ∃ v : WO S T, IsHalf (cA D E₂) v ∧ (∀ x ∈ stdHom S T, IsHalf E₂ x → ψ (symplO S T x v) = 1) ∧ u = r + k • v := by
  intro D ψ hψ S T Q E₂ hE k hk
  obtain ⟨N, hN, hup⟩ := GlobalTheory.T.exists_nsmul_annihilator_half_mem_standardHom D ψ hψ S T Q E₂ hE
  obtain ⟨M, hM, hlow⟩ := GlobalTheory.StdHomOrth.exists_nsmul_orth D ψ hψ S T
  obtain ⟨Q', hQ'⟩ := GlobalTheory.T.exists_isIdemSum_conj_of_isIdemSum D Q E₂ hE
  have hAL : ∀ a ∈ annHalf ψ S T E₂, N • a ∈ stdHalf S T (cA D E₂) := fun a ha =>
    ⟨hup a ha.1 ha.2, half_nsmul ha.1 N⟩
  have hLA : ∀ l ∈ stdHalf S T (cA D E₂), M • l ∈ annHalf ψ S T E₂ := fun l hl =>
    ⟨half_nsmul hl.2 M, fun x hx _ => hlow x hx l hl.1⟩
  have hfin : ∀ j : ℕ, 0 < j → ∃ R : Finset (WO S T), ∀ u ∈ stdHalf S T (cA D E₂), ∃ r ∈ R,
      ∃ v ∈ stdHalf S T (cA D E₂), u = r + j • v := by
    intro j hj
    obtain ⟨R, hR⟩ := GlobalTheory.HalfStdFin.exists_reps_half_stdHom D S T Q' (cA D E₂) hQ' j hj
    refine ⟨R, fun u hu => ?_⟩
    obtain ⟨r, hr, v, hv, hvh, huv⟩ := hR u hu.1 hu.2
    exact ⟨r, hr, v, ⟨hv, hvh⟩, huv⟩
  obtain ⟨R, hR⟩ := GlobalTheory.addSubgroup_finite_quot_of_commensurable (WO S T) (annHalf ψ S T E₂) (stdHalf S T (cA D E₂))
    N M hN hM (nsmul_eq_zero_WO S T hN) hAL hLA hfin k hk
  refine ⟨R, fun u hu hann => ?_⟩
  obtain ⟨r, hr, v, hv, huv⟩ := hR u ⟨hu, hann⟩
  exact ⟨r, hr, v, hv.1, hv.2, huv⟩

end GlobalTheory.AnnConjHalf

end
end
end
