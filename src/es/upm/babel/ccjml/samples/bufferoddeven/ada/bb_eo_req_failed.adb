--  bb.adb --  Implements a one-item buffer with even/odd requests
--
--  Author : Manuel Carro

--  Even/Odd buffer.   We try to  be smart here, and  save complexity,
--  code, and memory  space.  The strategy is as  follows : we request
--  only odd  and even items.  If there  is no item, then  no Get call
--  should proceed.  No problem on  that.  Otherwise, there is an even
--  or  odd item, and  therefore, at  any given  time, and  with items
--  present, only  one type of call  should be blocked.  If  we do not
--  mind which task is the first  to wakeup, then all the tasks of the
--  same type can be queued  in the same entry.  Assume several "Even"
--  tasks are enqueued.  If there is an Odd number, and a new Odd call
--  comes from  outside, then it  can be serviced immediately,  and so
--  there is no need to requeue  it.  If there is an Even number, then
--  the calls  already enqueued have preference.  Therefore  it is not
--  necessary to  enqueue more  than one type  of calls at  any moment
--  (provided  the toplevel  entry  is protected  by  an existence  of
--  item).


--  The code below exemplifies the above line of reasoning.  Alas, it does
--  not work.  What is wrong with the code or with the reasoning?

with Conc_IO;
use Conc_IO;

procedure Bb_Eo_Req_Failed is

   subtype Item_Type is Natural;

   Num_Consumers : constant Positive := 9;
   Num_Producers : constant Positive := 3;

   --  Constants and type definitions

   type Request_Type is (Even, Odd);

   protected type Buffer is
      --  Get can request an even item or an odd item at will.
      entry Get
        (Req : in     Request_Type;
         What : out Item_Type);
      --  Put can leave an even item or an odd item as dictated by the
      --  caller task.
      entry Put
        (What : in Item_Type);
   private
      Item : Item_Type;
      Item_Present : Boolean := False;
      Delayed_Request : Request_Type;
      entry Delayed_Get
        (Req : in     Request_Type;
         What : out Item_Type);
   end Buffer;

   protected body Buffer
   is
      entry Get
        (Req : in     Request_Type;
         What : out Item_Type)
      when Item_Present is
      begin --  We have an item; is it what we need?
         if (Req = Even) = (Item mod 2 = 0) then   --  We got it! Serve, then.
            What := Item;
            Item_Present := False;
         else
            Delayed_Request := Req;
            requeue Delayed_Get;
         end if;
      end Get;

      entry Delayed_Get
        (Req : in     Request_Type;
         What : out Item_Type)
      when (Delayed_Request = Even) =  (Item mod 2 = 0) is
      begin
         What := Item;
         Item_Present := False;
      end Delayed_Get;

      entry Put
        (What : in Item_Type)
      when not Item_Present is
      begin
         Item := What;
         Item_Present := True;
      end Put;
   end Buffer;

   Pool : Buffer;

   --  Each producer and consumer is a task
   task type Producer_Type;
   task body Producer_Type is
      Item : Item_Type := Item_Type'First;   --  Make every producer to produce
                                             --  different items
   begin
      loop
         delay 0.5;
         Pool.Put (Item);
         Put_Line ("Task PUT item " & Item_Type'Image (Item));
         Item := Item_Type'Succ (Item) mod 17;
      end loop;
   end Producer_Type;

   task type Consumer_Type (Which_Type : Request_Type);
   task body Consumer_Type is
      Item : Item_Type;
   begin
      loop
         Pool.Get (Which_Type, Item);
         Put_Line ("Task GOT item " & Item_Type'Image (Item));
      end loop;
   end Consumer_Type;

   --  Start a number of producers and consumers just by declarating them as
   --  components of an array.
   Consumers_Even : array (1 .. Num_Consumers / 2) of Consumer_Type (Even);
   Consumers_Odd : array (1 .. Num_Consumers / 2) of Consumer_Type (Odd);
   Producers : array (1 .. Num_Producers) of Producer_Type;

begin
   null;
end Bb_Eo_Req_Failed;
