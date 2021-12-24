/*!
  \file aig_algebraic_rewriting.hpp
  \brief AIG algebraric rewriting

  EPFL CS-472 2021 Final Project Option 1
*/

#pragma once

#include "../networks/aig.hpp"
#include "../views/depth_view.hpp"
#include "../views/topo_view.hpp"

namespace mockturtle
{

namespace detail
{

template<class Ntk>
class aig_algebraic_rewriting_impl
{
  using node = typename Ntk::node;
  using signal = typename Ntk::signal;

public:
  aig_algebraic_rewriting_impl( Ntk& ntk )
    : ntk( ntk )
  {
    static_assert( has_level_v<Ntk>, "Ntk does not implement depth interface." );
  }

  void run()
  {
    bool cont{true}; /* continue trying */
    while ( cont )
    {
      cont = false; /* break the loop if no updates can be made */
      ntk.foreach_gate( [&]( node n ){
        if ( try_algebraic_rules( n ) )
        {
          ntk.update_levels();
          cont = true;
        }
      });
    }
  }

private:
  /* Try various algebraic rules on node n. Return true if the network is updated. */
  bool try_algebraic_rules( node n )
  {
    if ( try_associativity( n ) )
      return true;
    if ( try_distributivity( n ) )
      return true;
    if ( try_3l_distributivity( n ) )
      return true;

    return false;
  }

  bool extract_and( node n, signal* sl, signal* sr, node* nl, node* nr )
  {
    if ( ntk.fanin_size( n ) != 2 )
    {
      return false;
    }

    ntk.foreach_fanin( n, [&]( signal s, uint32_t i ){
      switch (i) {
      case 0:
        if ( sl )
        {
          *sl = s;
        }
        if ( nl )
        {
          *nl = ntk.get_node( s );
        }
        break;
      case 1:
        if ( sr )
        {
          *sr = s;
        }
        if ( nr )
        {
          *nr = ntk.get_node( s );
        }
      }
    });

    return true;
  }

  /* Try the associativity rule on node n. Return true if the network is updated. */
  bool try_associativity( node n )
  {
    signal sl, sr;
    node nl, nr;
    if ( !extract_and( n, &sl, &sr, &nl, &nr ) )
    {
      return false;
    }

    if ( ntk.level( nl ) > ntk.level( nr ) + 1 )
    {
      std::swap( sl, sr );
      std::swap( nl, nr );
    }
    else if ( ntk.level( nl ) + 1 >= ntk.level( nr ) )
    {
      return false;
    }

    if ( ntk.is_complemented( sr ) )
    {
      return false;
    }

    signal srl, srr;
    node nrl, nrr;
    if ( !extract_and( nr, &srl, &srr, &nrl, &nrr ) )
    {
      return false;
    }

    if ( ntk.level( nrl ) > ntk.level( nrr ) )
    {
      std::swap( nrl, nrr );
      std::swap( srl, srr );
    }
    else if ( ntk.level( nrl ) == ntk.level( nrr ) )
    {
      return false;
    }

    signal new_sl = ntk.create_and( sl, srl );
    signal new_s = ntk.create_and( new_sl, srr );
    ntk.substitute_node( n, new_s );
    return true;
  }

  /* Try the distributivity rule on node n. Return true if the network is updated. */
  bool try_distributivity( node n )
  {
    signal sl, sr;
    node nl, nr;
    if ( !extract_and( n, &sl, &sr, &nl, &nr ) )
    {
      return false;
    }

    if ( !ntk.is_complemented( sl ) || !ntk.is_complemented( sr ) )
    {
      return false;
    }

    signal sll, slr;
    node nll, nlr;
    if ( !extract_and( nl, &sll, &slr, &nll, &nlr ) )
    {
      return false;
    }

    signal srl, srr;
    node nrl, nrr;
    if ( !extract_and( nr, &srl, &srr, &nrl, &nrr ) )
    {
      return false;
    }

    if ( nll == nrr )
    {
      std::swap( sll, slr );
      std::swap( nll, nlr );
      std::swap( srl, srr );
      std::swap( nrl, nrr );
    }
    else if ( nll == nrl )
    {
      std::swap( sll, slr );
      std::swap( nll, nlr );
    }
    else if ( nlr == nrr )
    {
      std::swap( srl, srr );
      std::swap( nrl, nrr );
    }
    else if ( nlr != nrl )
    {
      return false;
    }

    if ( ntk.level( nlr ) <= ntk.level( nll ) || ntk.level( nlr ) <= ntk.level( nrr ) )
    {
      return false;
    }

    if ( ntk.is_complemented( slr ) != ntk.is_complemented( srl ) )
    {
      return false;
    }

    signal new_sl = slr;
    signal new_srl = ntk.create_not( sll );
    signal new_srr = ntk.create_not( srr );
    signal new_sr = ntk.create_nand( new_srl, new_srr );
    signal new_s = ntk.create_nand( new_sl, new_sr );
    ntk.substitute_node( n, new_s );
    return true;
  }

  /* Try the three-layer distributivity rule on node n. Return true if the network is updated. */
  bool try_3l_distributivity( node n )
  {
    signal sl, sr;
    node nl, nr;
    if ( !extract_and( n, &sl, &sr, &nl, &nr ) )
    {
      return false;
    }

    if ( ntk.level( nl ) > ntk.level( nr ) + 2 )
    {
      std::swap( sl, sr );
      std::swap( nl, nr );
    }
    else if ( ntk.level( nl ) + 2 >= ntk.level( nr ) )
    {
      return false;
    }

    if ( !ntk.is_complemented( sr ) )
    {
      return false;
    }

    signal srl, srr;
    node nrl, nrr;
    if ( !extract_and( nr, &srl, &srr, &nrl, &nrr ) )
    {
      return false;
    }

    if ( ntk.level( nrl ) > ntk.level( nrr ) + 1 )
    {
      std::swap( srl, srr );
      std::swap( nrl, nrr );
    }
    else if ( ntk.level( nrl ) + 1 >= ntk.level( nrr ) )
    {
      return false;
    }

    if ( !ntk.is_complemented( srr ) )
    {
      return false;
    }

    signal srrl, srrr;
    node nrrl, nrrr;
    if ( !extract_and( nrr, &srrl, &srrr, &nrrl, &nrrr ) )
    {
      return false;
    }

    if ( ntk.level( nrrl ) > ntk.level( nrrr ) )
    {
      std::swap( srrl, srrr );
      std::swap( nrrl, nrrr );
    }
    else if ( ntk.level( nrrl ) == ntk.level( nrrr ) )
    {
      return false;
    }

    signal new_sll = sl;
    signal new_slr = ntk.create_not( srl );
    signal new_sl = ntk.create_nand( new_sll, new_slr );
    signal new_srll = sl;
    signal new_srlr = srrl;
    signal new_srl = ntk.create_and( new_srll, new_srlr );
    signal new_srr = srrr;
    signal new_sr = ntk.create_nand( new_srl, new_srr );
    signal new_s = ntk.create_nand( new_sl, new_sr );
    ntk.substitute_node( n, new_s );
    return true;
  }

private:
  Ntk& ntk;
};

} // namespace detail

/* Entry point for users to call */
template<class Ntk>
void aig_algebraic_rewriting( Ntk& ntk )
{
  static_assert( std::is_same_v<typename Ntk::base_type, aig_network>, "Ntk is not an AIG" );

  depth_view dntk{ntk};
  detail::aig_algebraic_rewriting_impl p( dntk );
  p.run();
}

} /* namespace mockturtle */
