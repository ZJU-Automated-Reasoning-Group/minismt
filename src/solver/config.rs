/// Configuration options for the SMT solver
#[derive(Clone, Debug)]
pub struct SolverConfig {
    /// Enable model checking (verify model satisfies assertions)
    pub check_model: bool,
    
    /// Enable local constant folding (e.g., 2+3 -> 5)
    pub enable_local_simp: bool,
    
    /// Enable global simplifications (e.g., caching, CSE)
    pub enable_global_simp: bool,
    
    /// Enable rewrite rules (e.g., x+0 -> x, x*1 -> x)
    pub enable_rewrites: bool,
    
    /// Enable constant propagation through operations
    pub enable_const_prop: bool,
    
    /// Enable bitblasting optimizations
    pub enable_bitblast_opts: bool,
}

impl Default for SolverConfig {
    fn default() -> Self {
        Self {
            check_model: false,
            enable_local_simp: true,
            enable_global_simp: true,
            enable_rewrites: true,
            enable_const_prop: true,
            enable_bitblast_opts: true,
        }
    }
}

impl SolverConfig {
    pub fn new() -> Self {
        Self::default()
    }
    
    /// Create config with all optimizations disabled
    pub fn no_opts() -> Self {
        Self {
            check_model: false,
            enable_local_simp: false,
            enable_global_simp: false,
            enable_rewrites: false,
            enable_const_prop: false,
            enable_bitblast_opts: false,
        }
    }
    
    /// Create config with only basic features enabled
    pub fn basic() -> Self {
        Self {
            check_model: false,
            enable_local_simp: false,
            enable_global_simp: false,
            enable_rewrites: false,
            enable_const_prop: false,
            enable_bitblast_opts: false,
        }
    }
}

