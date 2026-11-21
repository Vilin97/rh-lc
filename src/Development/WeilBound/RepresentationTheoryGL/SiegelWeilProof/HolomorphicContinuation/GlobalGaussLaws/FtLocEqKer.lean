module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ContinuousBw

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open Formalism.IndefR.Eqv (psiT eq_thetaC)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP
open Classical

variable {D : D7} {n m : ℕ}

def ker (ε : Fin m → Bool) (t : ℝ) (v u : Fin m → Fin n → ℂ) : ℂ :=
  Complex.exp (Complex.I * ((2 * t : ℝ) : ℂ) * (((Matrix.of v)ᴴ * Matrix.diagonal (sgn ε) * Matrix.of u).trace.re : ℂ))

theorem ftLoc_eq_ker (ε : Fin m → Bool) (t : ℝ) (f : (Fin m → Fin n → ℂ) → ℂ) (v : Fin m → Fin n → ℂ) :
    ftLoc ε t f v = ∫ u, f u * ker ε t v u := rfl


set_option synthInstance.maxHeartbeats 400000 in
theorem integrand_eq {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} {l : D.what₂.Tau → ℝ}
    (hl : HasRealPar ψ θ l) {V : HSp D} {τ : D.what₂.Tau} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsTauFrame V τ s ε fr)
    (f : (Fin V.rank → Fin n → ℂ) → ℂ) (Ψ : Mx D V.rank n → ℂ) (x y : Mx D V.rank n) :
    tens θ τ fr f Ψ y * ψ (trA (Matrix.trace (inner V x y))) =
      (f (piF θ τ fr y) * ker ε (tLoc l τ) (piF θ τ fr x) (piF θ τ fr y)) * Bw ψ V θ τ fr Ψ x y := by
  have hsplit : inner V x y = inner V x (y - sIns τ fr (piF θ τ fr y)) + inner V x (sIns τ fr (piF θ τ fr y)) := by
    rw [← GlobalTheory.CompanionTheory.EisCovar.Weyl.inner_add_right, sub_add_cancel]
  have hψ2 : ψ (trA (Matrix.trace (inner V x y))) =
      ψ (trA (Matrix.trace (inner V x (y - sIns τ fr (piF θ τ fr y))))) *
        ψ (trA (Matrix.trace (inner V x (sIns τ fr (piF θ τ fr y))))) := by
    rw [hsplit, Matrix.trace_add, GlobalTheory.CompanionTheory.EisCovar.Weyl.trA_add, AddChar.map_add_eq_mul]
  have map_inner_local (V : HSp D) (τ : D.what₂.Tau) (x y : Mx D V.rank n) :
      (inner V x y).map (psiT D τ) = (x.map (psiT D τ))ᴴ * (gramAt D V τ * y.map (psiT D τ)) := by
    have h1 : (adj x).map (psiT D τ) = (x.map (psiT D τ))ᴴ := by
      ext i j
      simp only [adj, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
      exact Formalism.IndefR.Eqv.psiT_sigR D τ (x j i)
    have h2 : (gA V).map (psiT D τ) = gramAt D V τ := by
      ext i j
      simp only [gA, rat, Matrix.map_apply, gramAt]
      exact Formalism.IndefR.Eqv.psiT_inclR D τ _
    show (adj x * (gA V * y)).map (psiT D τ) = _
    rw [Matrix.map_mul, Matrix.map_mul, h1, h2]
  have psiT_trace_local {a : ℕ} (τ : D.what₂.Tau) (M : Matrix (Fin a) (Fin a) (AE D)) :
      psiT D τ (Matrix.trace M) = Matrix.trace (M.map (psiT D τ)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
  have finPart_trace_local {a : ℕ} (M : Matrix (Fin a) (Fin a) (AE D)) :
      finPart D (Matrix.trace M) = Matrix.trace (M.map (finPart D)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
  have finMap_inner_local (V : HSp D) (x y : Mx D V.rank n) (hy : y.map (finPart D) = 0) :
      (inner V x y).map (finPart D) = 0 := by
    show (adj x * (gA V * y)).map (finPart D) = 0
    rw [Matrix.map_mul, Matrix.map_mul, hy, Matrix.mul_zero, Matrix.mul_zero]
  
  have psi_inner_sIns_local (x : Mx D V.rank n) (u : Fin V.rank → Fin n → ℂ) :
      ψ (trA (Matrix.trace (inner V x (sIns τ fr u)))) =
        Complex.exp (Complex.I * ((2 * tLoc l τ : ℝ) : ℂ) *
          (((Matrix.of (piF θ τ fr x))ᴴ * Matrix.diagonal (sgn ε) * Matrix.of u).trace.re : ℂ)) := by
    have hins : ∀ τ', (sIns (D := D) τ fr u).map (psiT D τ') = if τ' = τ then fr * Matrix.of u else 0 := by
      intro τ'
      have := compAt_insT (D := D) hθ τ τ' (fr * Matrix.of u)
      rw [eq_thetaC D hθ] at this
      exact this
    rw [psi_trA_tau hθ hl τ]
    · congr 2
      · simp only [tLoc]; push_cast; ring
      · rw [psiT_trace_local, map_inner_local, hins, if_pos rfl]
        congr 2
        obtain ⟨hdet, hg, -⟩ := hfr
        have hx : Matrix.of (piF θ τ fr x) = fr⁻¹ * x.map (psiT D τ) := by
          rw [eq_thetaC D hθ] ; rfl
        rw [hx, ← hg, Matrix.conjTranspose_mul]
        have hinv : (fr⁻¹)ᴴ * frᴴ = 1 := by
          rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.conjTranspose_one]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (fr⁻¹)ᴴ frᴴ, hinv, Matrix.one_mul]
    · intro τ' hne
      rw [psiT_trace_local, map_inner_local, hins, if_neg hne, Matrix.mul_zero, Matrix.mul_zero, Matrix.trace_zero]
    · rw [finPart_trace_local, finMap_inner_local V x (sIns τ fr u) (finMap_insT τ (fr * Matrix.of u)), Matrix.trace_zero]
  rw [hψ2, psi_inner_sIns_local]
  have hp : (fr⁻¹ * compAt θ τ y : Matrix (Fin V.rank) (Fin n) ℂ) = piF θ τ fr y := rfl
  unfold Bw tens ker
  rw [hp]
  ring

end PositivityTheory.Rg.Sw.Glob.FTH
