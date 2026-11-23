module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointFramesMoveRationalIsometryStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepDatumRationalUnitaryEquivariantStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumEquivariantRationalUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelPrimeFunctionalsMoveRationalLatticeAut
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixStepDatumEquivariantRationalUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalChangeIntertwinesRationalIsometriesStatement
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryAutColumnFieldOfStandardUnitaryMatrStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalCoordsConjUnitaryStandardForm

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelPrimeFunctionalsMoveRationalIsometry

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

namespace GlobalTheory.TwV

theorem funMoved_ptAd_rat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → ∀ (P : t.Pr.vT (t.word u)) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal),
        IsOver v (seamP t.seam P.1) →
        FunMoved t.seam ((St i hi).K β).lev P v h (iotaOf A i hi β P v h) (ratA D.host.F (A.crd i hi) * x₁.1) ((((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)).deco.1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPins hTie i hi β x x₁ γ hγ hx g hg p hp P v h hv
  have H := funMoved_ratA_act t.seam _ P v h _ _ _ g.1 1 (hp.fnl P v h hv)
  have e : ratA D.host.F (A.crd i hi) * x₁.1 = ratA D.host.F (seamGL t.seam g.1) * (ratA D.host.F (A.crd i hi) * x.1) := by
    rw [hx, hg, map_mul, map_mul, map_inv]; group
  rw [e]
  exact H

end GlobalTheory.TwV
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelPrimeFunctionalsMoveRationalIsometryStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.levelPrimeFunctionals_move_rationalIsometry : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → ∀ (P : t.Pr.vT (t.word u)) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal),
        IsOver v (seamP t.seam P.1) →
        FunMoved t.seam ((St i hi).K β).lev P v h (iotaOf A i hi β P v h) (ratA D.host.F (A.crd i hi) * x₁.1) ((((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)).deco.1) := by
  first | exact @GlobalTheory.TwV.funMoved_ptAd_rat | exact GlobalTheory.TwV.funMoved_ptAd_rat | (intros; apply GlobalTheory.TwV.funMoved_ptAd_rat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointLatticeMovedRationalIsometry

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwLatRat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem seam_lat_gmap {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (g : Sp X.E n ≃ₗ[X.E] Sp X.E n)
    (N : Submodule (𝓞 X.E) (Sp X.E n)) : s.lat (Formalism.HermitianLatticesTheory.gmap g N) = mvL (seamGL s g) (s.lat N) := by
  ext y
  rw [s.mem_lat]
  unfold mvL
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Formalism.L2.Col.mem_gmap] at hx
    refine ⟨s.vec (g.symm x), (s.mem_lat N _).2 ⟨_, hx, rfl⟩, ?_⟩
    show (seamGL s g : Matrix (Fin n) (Fin n) D.host.E) *ᵥ (fun l => s.iE (g.symm x l)) = fun l => s.iE (x l)
    rw [seamGL_mulVec, LinearEquiv.apply_symm_apply]
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x0, hx0, rfl⟩ := (s.mem_lat N w).1 hw
    refine ⟨g x0, ?_, ?_⟩
    · rw [Formalism.L2.Col.mem_gmap, LinearEquiv.symm_apply_apply]; exact hx0
    · show (fun l => s.iE (g x0 l)) = (seamGL s g : Matrix (Fin n) (Fin n) D.host.E) *ᵥ (fun l => s.iE (x0 l))
      rw [seamGL_mulVec]



theorem lat_moved : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → t.seam.lat ((((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)).deco.1.N = latCo D.sp (gramN D i hi) (A.crd i hi) a x₁.1 ((St i hi).K β).lev.Lb) := by
  intro D _ _ _ _ _ _ _ _ t u μ St A dtU a _ _ i hi β x x₁ γ hγ hx g hg p hp
  have e1 : ((((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)).deco.1.N = Formalism.HermitianLatticesTheory.gmap g.1 p.deco.1.N := rfl
  rw [e1, seam_lat_gmap, hg, hp.lat, hx, latCo_rat _ _ _ hγ]

end GlobalTheory.TwLatRat

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointLatticeMovedRationalIsometryStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.pointLattice_moved_rational_isometry : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → t.seam.lat ((((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)).deco.1.N = latCo D.sp (gramN D i hi) (A.crd i hi) a x₁.1 ((St i hi).K β).lev.Lb) := by
  first | exact @GlobalTheory.TwLatRat.lat_moved | exact GlobalTheory.TwLatRat.lat_moved | (intros; apply GlobalTheory.TwLatRat.lat_moved <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalUnitaryOrthonormalCoordsIsColumnIsometry

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.TwRat

theorem ratUnitCol : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (γ : GL (Fin (D.R.N i)) D.host.E), γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) →
      ∃ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹) := by
  intro D _ _ _ _ _ _ _ _ t u μ St A dtU a hP _ i hi γ hγ
  exact GlobalTheory.T.exists_unitaryAut_columnField_of_standard_unitary_matrix t.seam t.seam_ok (A.crd i hi * γ * (A.crd i hi)⁻¹)
    (GlobalTheory.unitary_conj_orthonormal D _ _ _ (hP.crd_orth i hi) hγ)

end GlobalTheory.TwRat
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalUnitaryOrthonormalCoordsIsColumnIsometryStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.rationalUnitary_orthonormalCoords_isColumnIsometry : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (γ : GL (Fin (D.R.N i)) D.host.E), γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) →
      ∃ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹) := by
  first | exact @GlobalTheory.TwRat.ratUnitCol | exact GlobalTheory.TwRat.ratUnitCol | (intros; apply GlobalTheory.TwRat.ratUnitCol <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicDatumRationalInvarianceOfKernelChain

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.RatPt

theorem isPtAd_rat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) ×
          GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie i hi β x x₁ γ hγ h₁ g hg p hp
  exact ⟨GlobalTheory.T.pointLattice_moved_rational_isometry A dtU a hP hTie i hi β x x₁ γ hγ h₁ g hg p hp, GlobalTheory.T.chartPointFrames_move_rationalIsometry A dtU a hP hTie i hi β x x₁ γ hγ h₁ g hg p hp,
    GlobalTheory.T.levelPrimeFunctionals_move_rationalIsometry A dtU a hP hTie i hi β x x₁ γ hγ h₁ g hg p hp⟩

theorem xiPt_smul : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m) β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) p p',
      IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      ∀ (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))) (w : HomE t.X.E (D.R.N i) (D.R.N (i + 1))),
      xiPt A i hi β β' (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)
        (((g', 1, 1) : UF t.X.E (D.R.N (i + 1)) × GLG (E := t.X.E) (n := D.R.N (i + 1)) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N (i + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p')
        (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = xiPt A i hi β β' p p' w) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie i hi
  rcases lt_trichotomy i t.m2 with h | h | h
  · exact GlobalTheory.T.matrixStepDatum_equivariant_rational_unitary A dtU a hP hTie i hi h
  · exact GlobalTheory.T.firstCoupledStepDatum_rationalUnitary_equivariant A dtU a hP hTie i hi h
  · exact GlobalTheory.T.lastStepDatum_equivariant_rationalUnitary A dtU a hP hTie i hi h

theorem ratLaw_of_tie : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    PtEx A a → (∀ i hi, PtAway A a i hi) → RatLaw A a) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie hEx hAw
  intro i hi β β' x x' x₁ x₁' γ hγ γ' hγ' h₁ h₁' z
  obtain ⟨g, hg⟩ := GlobalTheory.T.rationalUnitary_orthonormalCoords_isColumnIsometry A dtU a hP hTie i (Nat.le_of_succ_le hi) γ hγ
  obtain ⟨g', hg'⟩ := GlobalTheory.T.rationalUnitary_orthonormalCoords_isColumnIsometry A dtU a hP hTie (i + 1) hi γ' hγ'
  obtain ⟨p, hp⟩ := hEx i (Nat.le_of_succ_le hi) β x
  obtain ⟨p', hp'⟩ := hEx (i + 1) hi β' x'
  have hq := isPtAd_rat A dtU a hP hTie i (Nat.le_of_succ_le hi) β x x₁ γ hγ h₁ g hg p hp
  have hq' := isPtAd_rat A dtU a hP hTie (i + 1) hi β' x' x₁' γ' hγ' h₁' g' hg' p' hp'
  have hE1 : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x₁ p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x₁' p' := ⟨⟨_, hq⟩, ⟨_, hq'⟩⟩
  have hE0 : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x' p' := ⟨⟨_, hp⟩, ⟨_, hp'⟩⟩
  have a1 := hAw i hi β β' x₁ x₁' x₁ x₁' _ _ _ _ hq hq' hE1.1.choose_spec hE1.2.choose_spec (fun _ _ => ⟨rfl, rfl⟩)
  have a0 := hAw i hi β β' x x' x x' _ _ _ _ hp hp' hE0.1.choose_spec hE0.2.choose_spec (fun _ _ => ⟨rfl, rfl⟩)
  unfold xiAd
  rw [dite_eq_left hE1, dite_eq_left hE0, a1, a0, GlobalTheory.T.orthonormalChange_intertwines_rationalIsometries A dtU a hP hTie i hi γ γ' g g' hg hg' z]
  rw [xiPt_smul A dtU a hP hTie i hi β β' x x' p p' hp hp' g g']

end GlobalTheory.RatPt

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicDatumRationalInvarianceOfKernelChainStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.finiteAdelicDatum_rationalInvariance_of_kernelChain : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → (∀ i hi, PtAway A a i hi) → RatLaw A a) := by
  first | exact @GlobalTheory.RatPt.ratLaw_of_tie | exact GlobalTheory.RatPt.ratLaw_of_tie | (intros; apply GlobalTheory.RatPt.ratLaw_of_tie <;> assumption)
end
end
