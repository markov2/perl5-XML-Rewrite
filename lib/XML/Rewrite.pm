use warnings;
use strict;

package XML::Rewrite;
use base 'XML::Compile::Cache';

use Log::Report 'xml-rewrite', syntax => 'SHORT';

use XML::Compile::Util qw/pack_type type_of_node unpack_type SCHEMA2001/;
use XML::LibXML        ();

=chapter NAME

XML::Rewrite - schema based XML cleanups

=chapter SYNOPSIS

 my $rewriter = XML::Rewriter->new(...);
 my ($type, $data) = $rewriter->process($file);
 my $doc = $rewriter->buildDOM($type => $data);

=chapter DESCRIPTION
Often, XML messages and schemas are created by automatic tools.
These tools may provide very nice user interfaces, but tend to produce
horrible XML.  If you have to read these ugly products, you are in for
pain.  The purpose of this module (and the script C<xmlrewrite> which
is part of this distribution) is to be able to rewrite XML messages
and Schema's into something maintainable.

The main difference between this module and other beautifiers is that
the clean-up is based on schema rules.  For instance, it is permitted to
remove blanks around and inside integers, but not in strings. Beautifiers
which do not look into the schema have only limited possibilities for
cleanup, or may accidentally change the message content.

Feel invited to contribute ideas of useful features.

=chapter METHODS

=section Constructors

=c_method new [SCHEMA], OPTIONS
The rewrite object is based on an M<XML::Compile::Cache> object, which
defines the message structures.  The processing instructions can only
be specified at instance creation, because we need to be able to reuse
the compiled translators when we wish to process B<multiple messages>.

=default allow_undeclared <true>

=option  change 'REPAIR'|'TRANSFORM'
=default change 'TRANSFORM'
How to behave: either overrule the message settings (repair broken
messages), or to change the output.  If you wish both a correction and
a transformation, you will need to call the rewrite twice (create to
rewriter objects).

=option  output_encoding CHARSET
=default output_encoding <undef>
The character-set is usually copied from the source document, but
you can overrule this.  If neither the rewriter object nor the document
defined a encoding, then C<UTF-8> is used.

=option  output_version STRING
=default output_version <undef>
The XML version for the document.  This overrules the version found
in the document.  If neither is specified, then C<1.0> is used.

=option  output_compression -1, 0-8
=default output_compression <undef>
Set output compression level.  A value of C<-1> means that there should
be no compression.  By default, the compression level of the input
document is used.

=option  output_standalone BOOLEAN|'yes'|'no'
=default output_standalone <undef>
If specified, it will overrule the value found in the document.  If
not provided, the value from the source document will be used, but only
when present.

=default any_element   'ATTEMPT'
=default any_attribute 'ATTEMPT'

=option  use_default_namespace BOOLEAN
=default use_default_namespace <false>
If true, the blank prefix will be used for the first name-space needed
(usually the name-space of the top-level element).  Otherwise, the blank
prefix will not be used unless already defined explicitly in the provided
prefix table.

=option  remove_elements ARRAY
=default remove_elements []
All the selected elements are removed.  However: you shall not remove
elements which are required.

=option  defaults_writer 'EXTEND'|'IGNORE'|'MINIMAL'
=default defaults_writer 'IGNORE'
See M<XML::Compile::Schema::compile(default_values)>

=option  comments 'REMOVE'|'KEEP'
=default comments 'KEEP'
Comments found in the input may get translated in C<_COMMENT> and
C<_COMMENT_AFTER> fields in the intermediate HASH.    You may add
your own, before you reconstruct the DOM.  Comments are expected to
be used just before the element they belong to.

=option  blanks_before 'ALL'|'CONTAINERS'|'NONE'
=default blanks_before 'NONE'
Automatically put a blank line before each child of the root element, for
ALL childs, or only those which have childs themselves.  But _BLANK_LINE
in the HASH output of the reader, to change the selection on specific
locations.

=cut

sub init($)
{   my ($self, $args) = @_;

    $args->{any_element}   = 'ATTEMPT';
    $args->{any_attribute} = 'ATTEMPT';

    my $mode = $self->{XR_change} = $args->{change} || 'TRANSFORM';
    $mode eq 'REPAIR' || $mode eq 'TRANSFORM'
        or error __x"change mode must be either REPAIR or TRANSFORM, not `{got}'"
             , got => $mode;
    my $blanks = $self->{XR_blanks} = $args->{blanks_before} || 'NONE';
    $blanks eq 'ALL' || $blanks eq 'CONTAINERS' || $blanks eq 'ALL'
        or error __x"blanks_before must be ALL, CONTAINERS or ALL, not `{got}'"
             , got => $blanks;
 
    push @{$args->{opts_rw}}
      , mixed_elements     => 'STRUCTURAL'
      , use_default_namespace => $args->{use_default_namespace}
      , key_rewrite        => 'PREFIXED';

    my @read_hooks = ( {after => 'XML_NODE'} );
    foreach ( @{$args->{remove_elems}} )
    {   my $type = $self->findName($_) or next;
warn "REMOVE TYPE=$type not yet implemented";
    }

    my $comments = $args->{comments} || 'KEEP';
    if($comments eq 'KEEP')
    {   push @read_hooks, {after => \&take_comments_hook};
    }
    elsif($comments ne 'REMOVE')
    {   error __x"comment option either KEEP or REMOVE, not `{got}'"
           , got => $comments;
    }

    push @{$args->{opts_readers}}
      , hooks              => \@read_hooks
      , any_element        => ($args->{any_element} || 'CONVERT')
      , default_values     => 'IGNORE';

    my @write_hooks = +{after => sub {$self->nodeDataRelation(@_)}};

    push @{$args->{opts_writers}}
      , hooks              => \@write_hooks
      , include_namespaces => 1
      , ignore_unused_tags => qr/^_[A-Z_]*$/
      , default_values     => $args->{defaults_writer};

    defined $args->{allow_undeclared}
        or $args->{allow_undeclared} = 1;

    $self->SUPER::init($args);

    $self->{XR_encoding}   = $args->{output_encoding};
    $self->{XR_version}    = $args->{output_version};
    $self->{XR_alone}      = $args->{output_standalone};
    if(my $compr = $self->{XR_compress} = $args->{output_compression})
    {   $compr >= -1 && $compr <= 8
           or error __x"compression between -1 (off) and 8";
    }

    $self->{XR_prefixes}
     = [ map { $_->{prefix} => $_->{uri} } values %{$self->{XCC_prefix}} ];

    $self;
}

=section Processing

=method process XMLDATA, OPTIONS
XMLDATA must be XML as accepted by M<dataToXML()>.
Returned is LIST of two: the type of the data-structure read, and the
HASH representation of the contained data.

=option  type TYPE
=default type <from root element>
Explicit TYPE of the root element, required in case of namespace-less
elements or other namespace problems.
=cut

sub process($@)
{   my ($self, $xmldata, %args) = @_;

    # avoid the schema cache!
    my ($xml, %details) = XML::Compile->dataToXML($xmldata);
    my $type = $args{type} || type_of_node $xml;

    my $mode = $self->{XR_change};
    $self->repairXML($type, $xml, \%details)
        if $mode eq 'REPAIR';

    my $data = $self->reader($type)->($xml);

    $self->collectDocInfo($data, $xml);

    $self->transformData($type, $data, \%details)
        if $mode eq 'TRANSFORM';

    ($type, $data);
}

=method repairXML TYPE, XML, DETAILS
The TYPE of the root element, the root XML element, and DETAILS about
the xml origin.
=cut

sub repairXML($$$)
{   my ($self, $type, $xml, $details) = @_;
    trace "repairing XML";

    $self->repairNamespaces($xml);
    $self;
}

sub repairNamespaces($)
{   my ($self, $top) = @_;

    my @kv = @{$self->{XR_prefixes}};
    while(@kv)
    {   my ($prefix, $uri) = (shift @kv, shift @kv);
           $top->setNamespaceDeclURI($prefix, $uri)
        or $top->setNamespace($uri, $prefix, 0);
        $self->{XCC_prefix}{$uri}{used}++;
    }
    $self;
}

sub collectDocInfo($$)
{   my ($self, $data, $xml) = @_;

    if(my $doc  = $xml->ownerDocument)
    {   my $info = $data->{_DOC_INFO} ||= {};
        $info->{encoding}   = $doc->encoding;
        $info->{version}    = $doc->version;
        $info->{standalone} = $doc->standalone;
        $info->{compress}   = $doc->compression;
    }
    $data;
}

=method transformData TYPE, DATA, DETAILS
The TYPE of the root element, the HASH representation of the DATA of the
message, and DETAILS about the xml origin.
=cut

sub transformData($$$)
{   my ($self, $type, $data, $details) = @_;
    trace "transforming data structure";

    $self->transformDoc($data);
    $data;
}

sub transformDoc($)
{   my ($self, $data) = @_;

    my $di = $data->{_DOC_INFO} || {};

    $di->{version}   = $self->{XR_version}   if $self->{XR_version};
    $di->{version} ||= '1.0';

    $di->{encoding}   = $self->{XR_encoding} if $self->{XR_encoding};
    $di->{encoding} ||= 'UTF-8';

    $di->{compress}  = $self->{XR_compress}  if $self->{XR_compress};

    my $a = defined $self->{XR_alone} ? $self->{XR_alone} : $self->{XR_alone};
    if(defined $a)
    {   $di->{standalone} = $a eq 'no' || $a eq '0' ? 0 : 1;
    }

    $self;
}

=method buildDOM TYPE, DATA, OPTIONS
=cut

sub buildDOM($$@)
{   my ($self, $type, $data, %args) = @_;

    my $di   = $data->{_DOC_INFO} or panic "no doc-info";
    my $doc  = XML::LibXML::Document->new($di->{version}, $di->{encoding});

    $self->{XR_node_data} = [];
    my $out  = $self->writer($type)->($doc, $data);
    $doc->setDocumentElement($out) if $out;
    $self->postProcess($doc, $self->{XR_node_data});

    $doc->setCompression($di->{compress});
    $doc->setStandalone($di->{alone}) if defined $di->{alone};
    $doc;
}

sub take_comments_hook($$$)
{   my ($xml, $data, $path) = @_;
    my $previous = $xml;
    while($previous = $previous->previousSibling)
    {   last if $previous->isa('XML::LibXML::Element');
        unshift @{$data->{_COMMENT}}, $previous->textContent
             if $previous->isa('XML::LibXML::Comment');
    }
    $data;
}

sub nodeDataRelation($$$$)
{   my ($self, $doc, $node, $path, $data) = @_;
    push @{$self->{XR_node_data}}, [ $node, $data ];
    $node;
}

sub postProcess($$)
{   my ($self, $doc, $r) = @_;
    my $blanks = $self->{XR_blanks};

    while(@$r)
    {   my ($node, $data) = @{shift @$r};
        my $parent = $node->parentNode;
        next if $parent->isa('XML::LibXML::DocumentFragment'); # unattached

        my $b = $data->{_COMMENT} || [];
        my @b = map {$doc->createComment($_)} ref $b eq 'ARRAY' ? @$b : $b;

        my $grannie = $parent->parentNode;

        my $add_blank
          = @b                          ? 1  # before comments
          : exists $data->{_BLANK_LINE} ? $data->{_BLANK_LINE}
          : $blanks eq 'NONE'           ? 0
          : !($grannie && $grannie->isa('XML::LibXML::Document')) ? 0
          : $node->hasChildNodes        ? 1
          :                               ($blanks eq 'ALL');

        unshift @b, $doc->createTextNode('')
            if $add_blank;

        $parent->insertBefore($_, $node) for @b;

        my $a = $data->{_COMMENT_AFTER} || [];
        my @a = map {$doc->createComment($_)} ref $a eq 'ARRAY' ? @$a : $a;
        $parent->insertAfter($_, $node) for @a;
    }
}

1;
