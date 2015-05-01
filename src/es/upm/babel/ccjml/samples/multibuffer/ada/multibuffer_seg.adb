--  multibuffer_seg.adb --  Solución para el problema del multibuffer
--  con requeue; sólo seguridad
--
--  Author : Manuel Carro

--  with Ada.Text_Io;
--  use Ada.Text_Io;

with Conc_IO;
use Conc_IO;

with Ada.Numerics.Discrete_Random;

procedure Multibuffer_Seg is

   Num_Consumers : constant Positive := 3;
   Num_Producers : constant Positive := 3;

   --  The bounded buffer is a protected object with synchronization

   --  Constants and type definitions
   --  They cannot go into the object : only the state lives there!
   Buffer_Size : constant Natural := 10;

   --  A modular type gives a shorter and more readable code
   subtype Buffer_Quantity is Natural range 0 .. Buffer_Size;

   --  random generation of amounts of items to get or to put
   --  The maximum number of data which can be added to/retrieved from the
   --  array is Buffer_Size/2, in order to avoid interlocking.
   subtype Random_Range is Buffer_Quantity range 1 .. Buffer_Size;

   package Random_Amount is
      new Ada.Numerics.Discrete_Random (Random_Range);
   use Random_Amount;

   protected type MultiBuffer is
      entry Get (Items : in Random_Range);
      entry Put (Items : in Random_Range);
   private
      --  Number of items currently in the array
      Item_Counter : Buffer_Quantity := 0;
      --  Private entries for second phase of the lock
      entry Get_Fam (Random_Range) (Items : in Random_Range);
      entry Put_Fam (Random_Range) (Items : in Random_Range);
   end MultiBuffer;

   protected body MultiBuffer
   is
      entry Get (Items : in Random_Range)
      when True is
      begin
         requeue Get_Fam (Items);
      end Get;

      entry Get_Fam (for Q in Random_Range)
        (Items : in Random_Range)
      when Q <= Item_Counter is
      begin
         Item_Counter := Item_Counter - Q;
      end Get_Fam;

      entry Put (Items : in Random_Range)
      when True is
      begin
         requeue Put_Fam (Items);
      end Put;

      entry Put_Fam (for Q in Random_Range)
        (Items : in Random_Range)
      when Q <= Buffer_Size - Item_Counter is
      begin
         Item_Counter := Item_Counter + Q;
      end Put_Fam;

   end MultiBuffer;


   Pool : MultiBuffer;

   --  Each producer and consumer is a task

   task type Producer_Type;
   task body Producer_Type is
      Num : Random_Range;
      G : Generator;
   begin
      Reset (G);
      loop
         delay 0.2; --  Produce data (Item)
         Num := Random (G);
         Put_Line ("Producer generates " &
                   Random_Range'Image (Num) &
                   " items");
         Pool.Put (Num);
         Put_Line ("Producer puts " &
                   Random_Range'Image (Num) &
                   " items");
      end loop;
   end Producer_Type;


   task type Consumer_Type;
   task body Consumer_Type is
      Num : Random_Range;
      G : Generator;
   begin
      Reset (G);
      loop
         Num := Random (G);
         Put_Line ("Consumer wants " & Random_Range'Image (Num) & " items");
         Pool.Get (Num);
         Put_Line ("Consumer gets " & Random_Range'Image (Num) & " items");
         delay 0.2; --  está consumiendo los datos (Item)
      end loop;

   end Consumer_Type;

   --  Start a number of producers and consumers just by declarating them as
   --  components of an array.
   Consumers : array (1 .. Num_Consumers) of Consumer_Type;
   Producers : array (1 .. Num_Producers) of Producer_Type;

begin
   null;
end Multibuffer_Seg;

