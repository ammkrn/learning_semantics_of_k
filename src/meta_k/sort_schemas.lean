import .meta_sort
import .meta_symbol
import .meta_pattern


-- List {s}
def List : #Sort → #Sort
| s := #sort "List" (lift [s])


def Set : #Sort → #Sort
| carrier := #sort ( "Set") (lift [carrier])

def Bag : #Sort → #Sort
| carrier := #sort ( "Bag") (lift [carrier])

def Bag_p (s : #Sort) (h : meta_sort_name s ≠ ( "Bag_p")) : #Sort :=
        #sort ( "Bag_p") (lift [s])


def Map : #Sort → #Sort → #Sort
| s s' := #sort ("Map") (lift [s, s'])


def Map_p (s : #Sort) (h : meta_sort_name s ≠ ( "Map_p")) : #Sort :=
         #sort ( "Map_p") (lift [s])

def Context : #Sort → #Sort → #Sort
| s s' := #sort ( "Context") (lift [s, s'])

