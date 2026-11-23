module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DenseD
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
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
public import Formalism.LocalToGlobal.IndefiniteReal.DatumLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharDual

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DenseB

section

@[expose] public section

noncomputable section

open Matrix Topology

namespace PositivityTheory.Rg.Sw.Glob.DenseP

variable {n : ℕ}

theorem inG_nUh {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : InG (nU b) := by
  simp only [InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hb]
  simp

theorem inG_mL {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsUnit A.det) : InG (fromBlocks A 0 0 (A⁻¹)ᴴ) := by
  have h1 : Aᴴ * (A⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hA, Matrix.conjTranspose_one]
  have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ hA
  simp only [InG, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_zero]
  simp [h1, h2]

def hpart (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (A + Aᴴ)

theorem hpart_herm (A : Matrix (Fin n) (Fin n) ℂ) : (hpart A)ᴴ = hpart A := by
  simp only [hpart, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
  rw [add_comm]
  congr 1
  simp

theorem hpart_of_herm {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : hpart b = b := by
  rw [hpart, hb, ← two_smul ℂ b, smul_smul]; norm_num

def nuE (A : Matrix (Fin n) (Fin n) ℂ) : GR n := mkGR (nU (hpart A)) (inG_nUh (hpart_herm A))

theorem continuous_hpart : Continuous (hpart (n := n)) := by
  have h : Continuous fun A : Matrix (Fin n) (Fin n) ℂ => A + Aᴴ :=
    (continuous_id (X := Matrix (Fin n) (Fin n) ℂ)).add (continuous_id (X := Matrix (Fin n) (Fin n) ℂ)).matrix_conjTranspose
  exact h.const_smul (1 / 2 : ℂ)

theorem nU_mul_neg (b : Matrix (Fin n) (Fin n) ℂ) : nU b * nU (-b) = 1 := by
  simp [nU, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]

theorem continuous_nU : Continuous (nU (n := n)) :=
  Continuous.matrix_fromBlocks continuous_const continuous_id continuous_const continuous_const

theorem continuous_nuE : Continuous (nuE (n := n)) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · show Continuous fun A => nU (hpart A)
    exact continuous_nU.comp continuous_hpart
  · show Continuous fun A : Matrix (Fin n) (Fin n) ℂ => (nU (hpart A))⁻¹
    have e : (fun A : Matrix (Fin n) (Fin n) ℂ => (nU (hpart A))⁻¹) = fun A => nU (-hpart A) := by
      funext A
      exact Matrix.inv_eq_right_inv (nU_mul_neg _)
    rw [e]
    exact continuous_nU.comp continuous_hpart.neg


open Classical in
def mlE (A : Matrix (Fin n) (Fin n) ℂ) : GR n :=
  if h : IsUnit A.det then mkGR (fromBlocks A 0 0 (A⁻¹)ᴴ) (inG_mL h) else 1

theorem mlE_of {A : Matrix (Fin n) (Fin n) ℂ} (h : IsUnit A.det) :
    mlE A = mkGR (fromBlocks A 0 0 (A⁻¹)ᴴ) (inG_mL h) := by
  unfold mlE; exact dif_pos h

theorem isOpen_unitDet : IsOpen {A : Matrix (Fin n) (Fin n) ℂ | IsUnit A.det} := by
  have : {A : Matrix (Fin n) (Fin n) ℂ | IsUnit A.det} = (fun A : Matrix (Fin n) (Fin n) ℂ => A.det) ⁻¹' {z | z ≠ 0} :=
    Set.ext fun A => isUnit_iff_ne_zero
  rw [this]
  exact isOpen_ne.preimage (Continuous.matrix_det (continuous_id (X := Matrix (Fin n) (Fin n) ℂ)))

theorem continuousOn_inv_mat : ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℂ => A⁻¹) {A | IsUnit A.det} := by
  have e : (fun A : Matrix (Fin n) (Fin n) ℂ => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
    funext A; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [e]
  have h1 : ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℂ => (A.det)⁻¹) {A | IsUnit A.det} :=
    ContinuousOn.inv₀ (Continuous.matrix_det (continuous_id (X := Matrix (Fin n) (Fin n) ℂ))).continuousOn
      fun A hA => isUnit_iff_ne_zero.1 hA
  have h2 : Continuous fun A : Matrix (Fin n) (Fin n) ℂ => A.adjugate :=
    Continuous.matrix_adjugate (continuous_id (X := Matrix (Fin n) (Fin n) ℂ))
  exact h1.smul h2.continuousOn

theorem inv_mL {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsUnit A.det) :
    (fromBlocks A 0 0 (A⁻¹)ᴴ)⁻¹ = fromBlocks A⁻¹ 0 0 Aᴴ := by
  refine Matrix.inv_eq_right_inv ?_
  have h1 : (A⁻¹)ᴴ * Aᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hA, Matrix.conjTranspose_one]
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.mul_nonsing_inv _ hA, h1, ← Matrix.fromBlocks_one]

theorem continuousOn_mlE : ContinuousOn (mlE (n := n)) {A | IsUnit A.det} := by
  have hind : Topology.IsInducing (fun g : GR n => Units.embedProduct _ (g : GL (Fin n ⊕ Fin n) ℂ)) :=
    Units.isEmbedding_embedProduct.isInducing.comp Topology.IsInducing.subtypeVal
  rw [hind.continuousOn_iff]
  have hi := continuousOn_inv_mat (n := n)
  have hc : ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℂ =>
      (fromBlocks A 0 0 (A⁻¹)ᴴ, MulOpposite.op (fromBlocks A⁻¹ 0 0 Aᴴ))) {A | IsUnit A.det} := by
    rw [continuousOn_iff_continuous_restrict]
    have hi' : Continuous fun A : {A : Matrix (Fin n) (Fin n) ℂ | IsUnit A.det} => A.1⁻¹ := hi.restrict
    refine Continuous.prodMk ?_ ?_
    · exact Continuous.matrix_fromBlocks continuous_subtype_val continuous_const continuous_const
        hi'.matrix_conjTranspose
    · exact MulOpposite.continuous_op.comp (Continuous.matrix_fromBlocks hi' continuous_const continuous_const
        continuous_subtype_val.matrix_conjTranspose)
  refine ContinuousOn.congr hc fun A hA => ?_
  simp only [Function.comp_apply, mlE_of hA]
  show ((fromBlocks A 0 0 (A⁻¹)ᴴ), MulOpposite.op (fromBlocks A 0 0 (A⁻¹)ᴴ)⁻¹) = _
  rw [inv_mL hA]

theorem nuE_mem_closure {K : Type} [Field K] (τ : K →+* ℂ) (hτ : DenseRange τ) (A : Matrix (Fin n) (Fin n) ℂ) :
    nuE A ∈ closure (Set.range fun e : Matrix (Fin n) (Fin n) K => nuE (e.map τ)) := by
  have hd : DenseRange (fun e : Matrix (Fin n) (Fin n) K => e.map τ) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => hτ
  have h1 : nuE A ∈ nuE '' closure (Set.range fun e : Matrix (Fin n) (Fin n) K => e.map τ) := by
    rw [hd.closure_range]; exact ⟨A, trivial, rfl⟩
  have h2 := image_closure_subset_closure_image continuous_nuE h1
  rwa [← Set.range_comp] at h2

theorem mlE_mem_closure {K : Type} [Field K] (τ : K →+* ℂ) (hτ : DenseRange τ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUnit A.det) :
    mlE A ∈ closure (mlE '' ({A | IsUnit A.det} ∩ Set.range fun e : Matrix (Fin n) (Fin n) K => e.map τ)) := by
  have hd : DenseRange (fun e : Matrix (Fin n) (Fin n) K => e.map τ) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => hτ
  have hc : ContinuousAt (mlE (n := n)) A := (continuousOn_mlE (n := n)).continuousAt (isOpen_unitDet.mem_nhds hA)
  rw [mem_closure_iff_nhds]
  intro t ht
  have h1 : mlE ⁻¹' t ∩ {A | IsUnit A.det} ∈ 𝓝 A := Filter.inter_mem (hc ht) (isOpen_unitDet.mem_nhds hA)
  obtain ⟨U, hU, hUo, hAU⟩ := mem_nhds_iff.1 h1
  obtain ⟨e, he⟩ := hd.exists_mem_open hUo ⟨A, hAU⟩
  exact ⟨mlE (e.map τ), (hU he).1, e.map τ, ⟨(hU he).2, e, rfl⟩, rfl⟩

end PositivityTheory.Rg.Sw.Glob.DenseP
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DenseC

section

@[expose] public section

noncomputable section

open Matrix Topology
open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DenseP

open Formalism.IndefR.Eqv (psiT psiT_inclR)

variable {D : D7} {n : ℕ}

theorem denseRange_of_not_isReal' {K : Type} [Field K] (σ : K →+* ℂ)
    (h : ¬ NumberField.ComplexEmbedding.IsReal σ) : DenseRange σ := by
  have hc : IsClosed (σ.fieldRange.topologicalClosure : Set ℂ) :=
    Subfield.isClosed_topologicalClosure _
  rcases Complex.subfield_eq_of_closed hc with h1 | h1
  · exfalso
    apply h
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have hx : σ x ∈ σ.fieldRange.topologicalClosure := Subfield.le_topologicalClosure _ ⟨x, rfl⟩
    rw [h1] at hx
    obtain ⟨r, hr⟩ := hx
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq, ← hr]
    exact Complex.conj_ofReal r
  · have : closure (Set.range σ) = Set.univ := by
      have := congrArg (fun S : Subfield ℂ => (S : Set ℂ)) h1
      exact this
    exact dense_iff_closure_eq.2 this

theorem tauE_not_real (τ : D.what₂.Tau) : ¬ NumberField.ComplexEmbedding.IsReal (tauE D τ) := by
  intro h
  rw [NumberField.ComplexEmbedding.isReal_iff] at h
  have h1 : starRingEnd ℂ (tauE D τ D.host.xi0) = tauE D τ D.host.xi0 := by
    have := congrArg (fun f : D.host.E →+* ℂ => f D.host.xi0) h
    simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this
  have h2 : tauE D τ (star D.host.xi0) = starRingEnd ℂ (tauE D τ D.host.xi0) := Formalism.IndefR.Eqv.tauE_star D τ _
  rw [Formalism.IndefR.Datum.Brg.star_purely_imaginary_eq_neg, map_neg, h1] at h2
  have h3 : tauE D τ D.host.xi0 = 0 := by
    have : (2 : ℂ) * tauE D τ D.host.xi0 = 0 := by linear_combination -h2
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero
  exact Formalism.IndefR.Fin.embedding_xi_zero_ne_zero ((map_eq_zero_iff _ (tauE D τ).injective).1 h3)

theorem denseRange_tauE (τ : D.what₂.Tau) : DenseRange (tauE D τ) := denseRange_of_not_isReal' _ (tauE_not_real τ)

theorem sig_apply (x : D.host.E) : D.sp.cm.sig x = star x := rfl

theorem cT_map_tauE (τ : D.what₂.Tau) {k : ℕ} (u : Matrix (Fin k) (Fin k) D.host.E) :
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) u).map (tauE D τ) = (u.map (tauE D τ))ᴴ := by
  ext i j
  simp [Formalism.UG.cT, Matrix.conjTranspose_apply, sig_apply, Formalism.IndefR.Eqv.tauE_star]

theorem block_matrix_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  rw [blk4, blk4, ← Matrix.submatrix_map, Matrix.fromBlocks_map]

theorem map0 (τ : D.what₂.Tau) : (0 : Matrix (Fin n) (Fin n) D.host.E).map (tauE D τ) = 0 :=
  map_zero (RingHom.mapMatrix (tauE D τ))

theorem map1 (τ : D.what₂.Tau) : (1 : Matrix (Fin n) (Fin n) D.host.E).map (tauE D τ) = 1 :=
  map_one (RingHom.mapMatrix (tauE D τ))

theorem mapn1 (τ : D.what₂.Tau) : (-1 : Matrix (Fin n) (Fin n) D.host.E).map (tauE D τ) = -1 := by
  show RingHom.mapMatrix (tauE D τ) (-1) = -1
  rw [map_neg, map_one]

theorem map_smul_E (τ : D.what₂.Tau) {k : ℕ} (c : D.host.E) (X : Matrix (Fin k) (Fin k) D.host.E) :
    (c • X).map (tauE D τ) = (tauE D τ c) • X.map (tauE D τ) := by
  ext i j; simp [Matrix.map_apply, Matrix.smul_apply]

theorem Jst_map (τ : D.what₂.Tau) : (Jst D n).map (tauE D τ) = Glob.reidx (JJ n) := by
  rw [Jst, block_matrix_map, map0, map1, mapn1]
  rfl

theorem reidx_mul (a b : M2 n) : Glob.reidx (a * b) = Glob.reidx a * Glob.reidx b := by
  simp [Glob.reidx, Matrix.submatrix_mul_equiv]

theorem reidx_one : Glob.reidx (1 : M2 n) = 1 := by
  simp [Glob.reidx, Matrix.submatrix_one_equiv]

theorem reidx_conjTranspose (a : M2 n) : Glob.reidx aᴴ = (Glob.reidx a)ᴴ := by
  simp [Glob.reidx, Matrix.conjTranspose_submatrix]

theorem inG_JJc : InG (JJ n) := by
  simp only [InG, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp

theorem mat_one : mat (1 : G D n) = 1 := by simp [mat]

theorem mat_mul (g h : G D n) : mat (g * h) = mat g * mat h := by simp [mat]

theorem ratPt_of (τ : D.what₂.Tau) (u : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (M : M2 n) (hM : InG M)
    (hu : u.map (tauE D τ) = Glob.reidx M) : ∃ γ ∈ GF D n, (mat γ).map (psiT D τ) = Glob.reidx M := by
  have hdet : IsUnit u.det := by
    have h1 : tauE D τ u.det = M.det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hu, Glob.reidx, Matrix.det_submatrix_equiv_self]
    have h2 : M.det ≠ 0 := (isUnit_det_of_inG hM).ne_zero
    refine isUnit_iff_ne_zero.2 fun h0 => h2 ?_
    rw [← h1, h0, map_zero]
  let U : GL (Fin (n + n)) D.host.E := ⟨u, u⁻¹, Matrix.mul_nonsing_inv u hdet, Matrix.nonsing_inv_mul u hdet⟩
  have hU : U ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) := by
    show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) u * Jst D n * u = Jst D n
    have key : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) u * Jst D n * u).map (tauE D τ) =
        (Jst D n).map (tauE D τ) := by
      rw [Matrix.map_mul, Matrix.map_mul, cT_map_tauE, Jst_map, hu, ← reidx_conjTranspose, ← reidx_mul, ← reidx_mul, hM]
    exact Matrix.map_injective (tauE D τ).injective key
  refine ⟨GlobalTheory.AdelicU.ratEmb D.sp.cm.sig (Jst D n) ⟨U, hU⟩, ?_, ?_⟩
  · show _ ∈ GlobalTheory.AdelicU.ratPts D.sp.cm.sig (Jst D n)
    rw [← GlobalTheory.AdelicU.range_ratEmb]; exact MonoidHom.mem_range.2 ⟨_, rfl⟩
  · show (u.map (inclR (AF D.host.F))).map (psiT D τ) = _
    rw [Matrix.map_map]
    have : (⇑(psiT D τ) ∘ ⇑(inclR (AF D.host.F))) = ⇑(tauE D τ) := funext fun e => psiT_inclR D τ e
    rw [this, hu]

def gam (D : D7) (n : ℕ) (τ : D.what₂.Tau) : Subgroup (GR n) where
  carrier := {y | ∃ γ ∈ GF D n, (mat γ).map (psiT D τ) = Glob.reidx (mR y)}
  one_mem' := ⟨1, one_mem _, by
    rw [mat_one, Matrix.map_one _ (map_zero _) (map_one _)]
    exact reidx_one.symm⟩
  mul_mem' := by
    rintro a b ⟨γ, hγ, ea⟩ ⟨γ', hγ', eb⟩
    refine ⟨γ * γ', mul_mem hγ hγ', ?_⟩
    rw [mat_mul, Matrix.map_mul, ea, eb]
    exact (reidx_mul _ _).symm
  inv_mem' := by
    rintro a ⟨γ, hγ, ea⟩
    refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
    have h1 : (mat γ⁻¹).map (psiT D τ) * (mat γ).map (psiT D τ) = 1 := by
      rw [← Matrix.map_mul, ← mat_mul, inv_mul_cancel, mat_one, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : Glob.reidx (mR a) * Glob.reidx (mR a⁻¹) = 1 := by
      rw [← reidx_mul]
      show Glob.reidx (mR (a * a⁻¹)) = 1
      rw [mul_inv_cancel]; exact reidx_one
    calc (mat γ⁻¹).map (psiT D τ) = (mat γ⁻¹).map (psiT D τ) * (Glob.reidx (mR a) * Glob.reidx (mR a⁻¹)) := by
          rw [h2, Matrix.mul_one]
      _ = Glob.reidx (mR a⁻¹) := by rw [← Matrix.mul_assoc, ← ea, h1, Matrix.one_mul]

theorem mkGR_ext {g : M2 n} (hg : InG g) {h : GR n} (e : mR h = g) : h = mkGR g hg :=
  Subtype.ext (Units.ext e)

theorem gens_mem (τ : D.what₂.Tau) (h : GR n) (hh : IsNElt h ∨ IsMElt h ∨ IsWElt h) :
    h ∈ (gam D n τ).topologicalClosure := by
  rcases hh with ⟨b, hb, e⟩ | ⟨A, hA, e⟩ | e
  · have hh : h = nuE b := by
      rw [mkGR_ext (inG_nUh (hpart_herm b)) (show mR h = nU (hpart b) by rw [hpart_of_herm hb]; exact e)]; rfl
    rw [hh]
    refine closure_mono ?_ (nuE_mem_closure (tauE D τ) (denseRange_tauE τ) b)
    rintro _ ⟨e', rfl⟩
    have hβ : ((2 : D.host.E)⁻¹ • (e' + Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e')).map (tauE D τ) =
        hpart (e'.map (tauE D τ)) := by
      rw [map_smul_E, Matrix.map_add _ (map_add (tauE D τ)), cT_map_tauE, map_inv₀, map_ofNat, hpart, one_div]
    obtain ⟨γ, hγ, he⟩ := ratPt_of τ (blk4 1 ((2 : D.host.E)⁻¹ • (e' + Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e')) 0 1)
      (nU (hpart (e'.map (tauE D τ)))) (inG_nUh (hpart_herm _)) (by
        rw [block_matrix_map, map0, map1, hβ]
        rfl)
    exact ⟨γ, hγ, he⟩
  · have hh : h = mlE A := by rw [mlE_of hA]; exact mkGR_ext (inG_mL hA) e
    rw [hh]
    refine closure_mono ?_ (mlE_mem_closure (tauE D τ) (denseRange_tauE τ) A hA)
    rintro _ ⟨B, ⟨hB, e', rfl⟩, rfl⟩
    have hdet : IsUnit e'.det := by
      have h1 : tauE D τ e'.det = (e'.map (tauE D τ)).det := by rw [RingHom.map_det, RingHom.mapMatrix_apply]
      refine isUnit_iff_ne_zero.2 fun h0 => (hB : IsUnit (e'.map (tauE D τ)).det).ne_zero ?_
      rw [← h1, h0, map_zero]
    have hcd : IsUnit (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e').det := by
      have h1 : tauE D τ (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e').det = ((e'.map (tauE D τ))ᴴ).det := by
        rw [RingHom.map_det, RingHom.mapMatrix_apply, cT_map_tauE]
      refine isUnit_iff_ne_zero.2 fun h0 => ?_
      have : ((e'.map (tauE D τ))ᴴ).det = 0 := by rw [← h1, h0, map_zero]
      rw [Matrix.det_conjTranspose, star_eq_zero] at this
      exact (hB : IsUnit (e'.map (tauE D τ)).det).ne_zero this
    have hinv : ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e')⁻¹).map (tauE D τ) =
        ((e'.map (tauE D τ))⁻¹)ᴴ := by
      rw [Matrix.conjTranspose_nonsing_inv, ← cT_map_tauE]
      refine (Matrix.inv_eq_right_inv ?_).symm
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hcd, Matrix.map_one _ (map_zero _) (map_one _)]
    obtain ⟨γ, hγ, he⟩ := ratPt_of τ (blk4 e' 0 0 (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e')⁻¹)
      (fromBlocks (e'.map (tauE D τ)) 0 0 ((e'.map (tauE D τ))⁻¹)ᴴ) (inG_mL hB) (by
        rw [block_matrix_map, hinv, map0]
        rfl)
    refine ⟨γ, hγ, ?_⟩
    rw [he, mlE_of hB]
    rfl
  · refine (gam D n τ).le_topologicalClosure ?_
    obtain ⟨γ, hγ, he⟩ := ratPt_of τ (Jst D n) (JJ n) inG_JJc (Jst_map τ)
    exact ⟨γ, hγ, by rw [he, e]⟩

theorem gam_dense (hgen : GenSt) (τ : D.what₂.Tau) (g : GR n) : g ∈ closure (gam D n τ : Set (GR n)) := by
  have h1 : Subgroup.closure {h : GR n | IsNElt h ∨ IsMElt h ∨ IsWElt h} ≤ (gam D n τ).topologicalClosure :=
    (Subgroup.closure_le _).2 fun h hh => gens_mem τ h hh
  exact h1 (hgen n g)

end PositivityTheory.Rg.Sw.Glob.DenseP
end
end
end
